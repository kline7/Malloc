#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);
static inline void both_unallocated(header * free_chunk,header * left_neighbor,header * right_neighbor);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);
static inline size_t calculate_block_size(size_t raw_size);
static inline header * normal_allocate(size_t raw_size);
static inline size_t find_spot(size_t raw_size);
static inline void move_allocation(header * block, size_t block_size);
static inline header * break_free_chunk(header * block, size_t block_size);
static inline header * create_free_block(size_t size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief helper to calculate block size
 *
 * @param raw_size number of bytes that is needed for block
 *
 * @return size of block required
 */
static inline size_t calculate_block_size(size_t raw_size){
  //add size of the header
  raw_size = raw_size + ALLOC_HEADER_SIZE;
  //make sure it is a multiple of 8
  if (raw_size % 8 != 0){
    raw_size += 8 - (raw_size % 8);
  }
  //make sure that it is larger then the lower bound
  if (raw_size < sizeof(header)){
    raw_size = sizeof(header);
  }

  return raw_size;
}
/**                                                                              
 * @brief helper to allocate block                                                                                                     
 *                                                                                                                                               
 * @param raw_size number of bytes that is needed for block                                                                                             
 *                                                                                                                                                                   
 * @return header
 */
static inline header * normal_allocate(size_t raw_size){
  //find where to alloc
  size_t id = find_spot(raw_size);

  if(id != (N_LISTS - 1)){
    struct header * block = freelistSentinels[id].next;
    //if the block is the same size you can allocate and return
    if (raw_size == get_size(block)) {
      set_state(block,ALLOCATED);
      block->next->prev = block->prev;
      block->prev->next = block->next;
      return (header*)(&block->data[0]);
    }else{
      //since the sizes don't match the block must be split
      struct header * new_header = get_header_from_offset(block, (get_size(block) - raw_size));
      set_size(block, (get_size(block) - raw_size));
      //the size and left_size need to be updated
      set_size_and_state(new_header,raw_size,ALLOCATED);
      new_header->left_size = get_size(block);
      struct header * right_neighbor = get_right_header(new_header);
      right_neighbor->left_size = raw_size;
      
      if (get_size(block) > ((id+1) *8) || get_size(block) < (id * 8 + 1)){
	move_allocation(block,get_size(block));
      }
      
      return (header*)(&new_header->data[0]);
    }
  }else{
    //we are at the last element in the free list
    struct header * free = &freelistSentinels[N_LISTS-1];
    struct header * iter = free->next;
    //get block to split
    while(iter != free){
      if(get_size(iter) >= raw_size + 32){
	struct header * _ret = break_free_chunk(iter,(raw_size));
	return (header *)(&_ret->data[0]);
      }else if(get_size(iter) == raw_size){
	set_state(iter,ALLOCATED);
	iter->next->prev = iter->prev;
	iter->prev->next = iter->next;
	return (header *)(&iter->data[0]);
      }
      iter = iter->next;
    }
  //if there's no more space a new free block must be initialized
  return create_free_block(raw_size);
  }
}

/*
 *@breif this will call allocate_chunk to get more memory and then coalese the chunks appropriately
 *
 *@param takes the raw_size of the block to be allocated
 *
 *@return we call the allocate_object again to allocate the chunk we initially wanted(we need to take off the 16 of the header so it isn't doubled when the size is adjusted)
 */
static inline header * create_free_block(size_t raw_size){
  //allocate
  struct header * new_freeblock = allocate_chunk(ARENA_SIZE);
  //get header
  struct header * neighbor = get_header_from_offset(new_freeblock,-32);

  if (get_state(neighbor) == FENCEPOST){
    //get the neighbor
    struct header * lleft_neighbor = get_header_from_offset(neighbor, -neighbor->left_size);
    //see if the neighbor is allocated or not
    if (get_state(lleft_neighbor) != UNALLOCATED){
    //if not unallocated join neighbor with free
      set_size_and_state(neighbor,(get_size(neighbor)+get_size(new_freeblock)+16),UNALLOCATED);

      struct header * free = &freelistSentinels[(N_LISTS - 1)];
      free->prev->next = neighbor;
      neighbor->prev = free->prev;
      free->prev = neighbor;
      neighbor->next = free;
      //make sure you dont forget to set the left_size
      struct header * left = get_header_from_offset(neighbor,get_size(neighbor));
      left->left_size = get_size(neighbor);
      
    }else{
    //if unallocated new freeblock joins
      set_size(lleft_neighbor,(get_size(lleft_neighbor)+get_size(new_freeblock)+32));
   
      lleft_neighbor->next->prev = lleft_neighbor->prev;
      lleft_neighbor->prev->next = lleft_neighbor->next;
      
      struct header * free = &freelistSentinels[(N_LISTS - 1)];
      free->next->prev = lleft_neighbor;
      lleft_neighbor->next = free->next;
      free->next = lleft_neighbor;
      lleft_neighbor->prev = free;
      //make sure the left_size is right
      struct header * left = get_header_from_offset(lleft_neighbor,get_size(lleft_neighbor));
      left->left_size = get_size(lleft_neighbor);
    }
    
  }else{
    //find the previous fencepost
    struct header * fence_post = get_header_from_offset(new_freeblock, -ALLOC_HEADER_SIZE);
    //put a new os chunk in that portion
    insert_os_chunk(fence_post);
    //add new free block to the freelist
    struct header * free = &freelistSentinels[(N_LISTS - 1)];
    free->prev->next = new_freeblock;
    new_freeblock->prev = free->prev;
    free->prev = new_freeblock;
    new_freeblock->next = free;

  }
  //once everything is setup we can malloc the block now
  raw_size -= ALLOC_HEADER_SIZE;
  return allocate_object(raw_size);
}

/*
 *@brief helper method for allocating to take a big free block and break it up
 *
 *@param the free block to break and allocate(block), the size of the allocation(block_size)
 *
 *@return the header * to the allocated block
 */
static inline header * break_free_chunk(header * block, size_t block_size){
  //set the size of the block to the new free block
  set_size(block,(get_size(block)-block_size));
  //create chunk for allocation
  struct header * actual_alloc = get_header_from_offset(block,get_size(block));
  set_size(actual_alloc,(block_size));
  //set left_size and allocated
  actual_alloc->left_size = get_size(block);
  set_state(actual_alloc,ALLOCATED);
  //set right neighbors left size to the allocated size
  struct header * right_neighbor = get_header_from_offset(actual_alloc,get_size(actual_alloc));
  right_neighbor->left_size = get_size(actual_alloc);

  size_t id = ((get_size(block) - ALLOC_HEADER_SIZE) / 8) -1;

  if ( id < (N_LISTS -1))
    {
      block->next->prev = block->prev;
      block->prev->next = block->next;
      struct header * free = &freelistSentinels[id];
      free->next->prev = block;
      block->next = free->next;
      free->next = block;
      block->prev = free;
    }
  
  return actual_alloc;
}

/*
 *@breif helper method to find a spot in the free list that will be used to allocate
 *
 *@param the raw_size of block to be allocated
 *
 *@return an index in the freelistSentinel to the appropriate free block size
 */
static inline size_t find_spot(size_t raw_size){
  //set the spot to start
  size_t to_ret = ((raw_size - ALLOC_HEADER_SIZE) / 8) - 1;
  //check to see if the size is larger then the list
  if (to_ret > N_LISTS-1){
    to_ret = N_LISTS - 1;
    return to_ret;
  }
  //spin through the freelist to find a place to put the block
  while (freelistSentinels[to_ret].next == &freelistSentinels[to_ret] && to_ret < (N_LISTS - 1)){
    to_ret++;
  }
  return to_ret;
}

/*
 *@brief helper method for manipulating the free block to break into the allocated and free portion
 *
 *@param block of allocation, size of the block 
 *
 *@return void method
 */
static inline void move_allocation(header * block,size_t block_size){
  size_t id = (block_size - ALLOC_HEADER_SIZE) / 8 - 1;
  //see if we need to put it at the end
  if(id > (N_LISTS - 1)){
      //put at the end
      //remove block                                                                                                                                                       
    block->prev->next = block->next;
    block->next->prev = block->prev;
      //put it back in
      freelistSentinels[(N_LISTS - 1)].prev->next = block;
      block->next = &freelistSentinels[(N_LISTS - 1)];
      block->prev = freelistSentinels[(N_LISTS - 1)].prev;
      freelistSentinels[(N_LISTS - 1)].prev = block;
      set_size(block,block_size);
      struct header * right_neighbor = get_right_header(block);
      right_neighbor->left_size = block_size;
    }else{
      //remove block
    block->prev->next = block->next;
    block->next->prev = block->prev;
      //put it back in
      freelistSentinels[id].next->prev = block;
      block->next = freelistSentinels[id].next;
      block->prev = &freelistSentinels[id];
      freelistSentinels[id].next = block;
      set_size(block,block_size);
      struct header * right_neighbor = get_right_header(block);
      right_neighbor->left_size = block_size;
    }
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  //if size is 0 ret null
  if (raw_size == 0){
    return NULL;
  }  
  //make sure malloc has been init
  if (!isMallocInitialized){
    //init();
    isMallocInitialized = 1;
  }
  //calc size of blck with alloc and unalloc header sizes
  size_t _actualsize = calculate_block_size(raw_size);
  //call helper to attempt to malloc
  return normal_allocate(_actualsize);
  
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation ;)
  //make sure they don't pull a fast one on you
  size_t size;
  int withinFree = 0;
  if (p == NULL){
    return;
  }
  //chunk of mem that wants to be free
  struct header * free_chunk = ptr_to_header(p);
  //TODO: add whatever needs to be done for double free
  if (get_state(free_chunk) == UNALLOCATED || free_chunk == NULL){
    //double free
    printf("Double Free Detected\n");
    printf("Assertion Failed!\n");
    exit(1);
    return;
  }
  //now set the chunk free
  set_state(free_chunk,UNALLOCATED);
  //let's meet the neighbors
  struct header * left_neighbor = get_left_header(free_chunk);
  struct header * right_neighbor = get_right_header(free_chunk);
  size_t id;
  
  if (get_state(left_neighbor) == UNALLOCATED && get_state(right_neighbor) == UNALLOCATED){
    //both neighbors are unallocated
    both_unallocated(free_chunk,left_neighbor,right_neighbor);
  }else if (get_state(left_neighbor) == UNALLOCATED){
    //left is unallocated
    set_state(free_chunk,UNALLOCATED);

    if (get_size(left_neighbor) > 512){
      withinFree = 1;
    }
    //the left_neighbor is a free block that you want to join with
    set_size(left_neighbor,(get_size(free_chunk)+get_size(left_neighbor)));
    size = get_size(left_neighbor);
    left_neighbor->next->prev = left_neighbor->prev;
    left_neighbor->prev->next = left_neighbor->next;

    if ( withinFree == 0){
    id = ((get_size(left_neighbor) - ALLOC_HEADER_SIZE) / 8) -1;
    struct header * freelist = NULL;
    //To make sure you go over the index
    if (get_size(left_neighbor) <= 512){
      freelist = &freelistSentinels[id];
    }else{
      freelist = &freelistSentinels[(N_LISTS - 1)];
    }

    //setup the freelist with new chunk
    freelist->next->prev = left_neighbor;
    left_neighbor->next = freelist->next;
    freelist->next = left_neighbor;
    left_neighbor->prev = freelist;
    }else if(withinFree == 1){
      //setup the pointers for left_neighbor
      left_neighbor->next->prev = left_neighbor;
      left_neighbor->prev->next = left_neighbor;
      left_neighbor->next = left_neighbor->next;
      left_neighbor->prev = left_neighbor->prev;
    }
    //the size of the right neighbor must be updated
    struct header * neighbor = get_header_from_offset(left_neighbor,get_size(left_neighbor));
    neighbor->left_size = get_size(left_neighbor);
    
  }else if (get_state(right_neighbor) == UNALLOCATED ){
    //right is unallocated
    set_state(free_chunk,UNALLOCATED);

    if (get_size(right_neighbor) > 512){
      withinFree = 1;
    }
    //set the size of the free chunk
    set_size(free_chunk,(get_size(free_chunk)+get_size(right_neighbor)));
    //size is the size of the free chunk to make things easier
    size = get_size(free_chunk);
    //get rid of the right neighbor
    right_neighbor->next->prev = right_neighbor->prev;
    right_neighbor->prev->next = right_neighbor->next;
    //set up the free list
    if (withinFree == 1){
      right_neighbor->next->prev = free_chunk;
      free_chunk->next = right_neighbor->next;
      right_neighbor->prev->next = free_chunk;
      free_chunk->prev = right_neighbor->prev;
    }else if(withinFree == 0){
      struct header * free = NULL;
      if (size <= 512){
	free = &freelistSentinels[((size - ALLOC_HEADER_SIZE)/8) - 1];
      }else{
	free = &freelistSentinels[(N_LISTS - 1)];
      }
      free->next->prev = free_chunk;
      free_chunk->next = free->next;
      free->next = free_chunk;
      free_chunk->prev = free;
    }
    
    //right neighbor's left size needs to be changed
    struct header * neighbor = get_header_from_offset(free_chunk,size);
    neighbor->left_size = size;
    
  }else{
    //both are allocated
    id = ((get_size(free_chunk) - ALLOC_HEADER_SIZE) / 8) - 1;
    //be free chunk
    set_state(free_chunk,UNALLOCATED);
    //make sure that it only is as big as free list
    if (id > (N_LISTS - 1)){
      id = N_LISTS - 1;
    }
    //setup the free list
    freelistSentinels[id].next->prev = free_chunk;
    free_chunk->next = freelistSentinels[id].next;
    freelistSentinels[id].next = free_chunk;
    free_chunk->prev = &freelistSentinels[id];
  }
}

/*
 *@brief if both left and right are unallocated for deallocation
 *
 *@param the block to be free, and the left and right neighbors
 *
 *@return void method
 */
static inline void both_unallocated(header * free_chunk,header * left_neighbor,header * right_neighbor){
  int withinFree = 0;
  size_t size;
  //both neighbors are unallocated                                                                                                                                                                      
    set_state(free_chunk,UNALLOCATED);
    //see if the block is larger then the list                                                                                                                                                           
    if(get_size(left_neighbor) > 512){
      withinFree = 1;
    }

    set_size(left_neighbor, (get_size(left_neighbor)+get_size(free_chunk)+get_size(right_neighbor)));
    size = get_size(left_neighbor);

    right_neighbor->next->prev = right_neighbor->prev;
    right_neighbor->prev->next = right_neighbor->next;

    left_neighbor->next->prev = left_neighbor->prev;
    left_neighbor->prev->next = left_neighbor->next;
    //fix up the free list depending on the size of the left block                                                                                                                                       
    if (withinFree == 1){
      left_neighbor->next->prev = left_neighbor;
      left_neighbor->next = left_neighbor->next;
      left_neighbor->prev->next = left_neighbor;
      left_neighbor->prev = left_neighbor->prev;
    }else if (withinFree == 0){
      struct header * free = NULL;
      if(size <= 512){
        free = &freelistSentinels[((size - ALLOC_HEADER_SIZE)/8)-1];
      }else{
        free = &freelistSentinels[(N_LISTS - 1)];
      }

      free->prev->next = left_neighbor;
      left_neighbor->next = free->next;
      free->next = left_neighbor;
      left_neighbor->prev = free;
    }
    //make sure the size of the right neighbor has the correct left size                                                                                                                                 
    struct header * neighbor = get_header_from_offset(left_neighbor,size);
    neighbor->left_size = size;
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
