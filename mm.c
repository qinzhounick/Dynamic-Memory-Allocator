/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based explicit free list memory allocator          *
 *                      with coalesce functionality                           *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *  Nick Song                                                                 *
 *  Dec 12, 2022                                                              *
 ******************************************************************************
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif


/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;    //set the prev_alloc bit mask
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    union {
        struct {
	    struct block* prev;  //use prev pointer for freelist linking
            struct block* next;  //use next pointer for freelist linking
	};

        char payload[0];
    };
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
static block_t *freelist_start;  /*declare a start for the explicit free list*/

bool mm_checkheap(int lineno);
//checkheap helper functions
void mm_printheap();
void mm_printfreelist();
bool check_freeblock_coalesce();
bool check_prev_alloc();
bool check_all_freeblocks_in_freelist();
bool check_if_size_smaller_than_minsize();
bool check_freelist_correctly_linked();
bool check_alloc_block_overlap();
bool check_pointer_valid();
/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
/*add prev_alloc parameter to remove footer*/
static word_t pack(size_t size, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

/*helper function to extract the prev_alloc bit*/
static bool extract_prev_alloc(word_t header);
/*helper function to get the prev allocation status*/
static bool get_prev_alloc(block_t *block);

/*add prev_alloc parameter*/
static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc);
/*add prev_alloc parameter*/
static void write_footer(block_t *block, size_t size, bool prev_alloc, bool alloc);
/*helper function to set the prev_alloc bit of the next block header*/
static void set_next_prev_alloc(block_t *block, bool prev_alloc);
/*helper function to set the prev_alloc bit of the next block footer*/
static void set_next_prev_alloc_footer(block_t *block, bool prev_alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/*
*Implement explicit free list
*free list remove and insert functions
*/

/*helper function to remove a block from the freelist*/
static void fl_remove(block_t *block){
    //dbg_printf("fl_remove: ");
    //dbg_printf("freelist_start: %p\n", freelist_start);
    //mm_printheap();
    if(block == NULL || get_alloc(block)){
        return;
    }

    block_t * nextptr = block->next;
    block_t * prevptr = block->prev;

    //set the next and prev pointer of current block to 0
    //  because it is removed from the free list
    block->next = NULL;
    block->prev = NULL;
    
    //if the prev and next pointers are both null, set freelist to null
    if(nextptr==NULL && prevptr==NULL){
        freelist_start = NULL;
    }
    //if only the prev pointer is null, set the start to next pointer
    else if(prevptr==NULL){
        nextptr->prev = NULL;
        freelist_start = nextptr;
    }
    //if only the next pointer is null, 
    //  set the next pointer of the prev pointer to NULL
    //  meaning the prev pointer is at the end of the list
    else if(nextptr==NULL){
        prevptr->next = NULL;
    }
    //if neither next nor prev pointer is null,
    //  set prev's next pointer to next
    //  set next's prev pointer to prev
    else{
        prevptr->next = nextptr;
        nextptr->prev = prevptr;
    }
    //dbg_printf("fl_remove end: %p\n", freelist_start);
    //mm_printheap();
}

/*helper function to insert block into freelist*/
static void fl_insert(block_t *block){
    //dbg_printf("fl_insert start: ");
    //dbg_printf("%p\n", freelist_start);
    //mm_printheap();
    if(block == NULL)
        return;
    //if the freelist is null set the block as the start
    if(freelist_start == NULL){
        freelist_start = block;
        //dbg_printf("fl_insert end: ");
        //dbg_printf("%p\n", freelist_start);
        //mm_printheap();
        return;
    }
    //set block as the start and make freelist point to the block
    block->next = freelist_start;
    freelist_start->prev = block;
    freelist_start = block;
    //dbg_printf("fl_insert end: ");
    //dbg_printf("%p\n", freelist_start);
    //mm_printheap();
}


/*
 * <what does mm_init do?>
 */
bool mm_init(void) 
{
    //dbg_printf("mm_init: \n");
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    freelist_start = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size) 
{
    //dbg_printf("malloc start: \n");
    //mm_printheap();
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    /*add only the header size to the given size 
          because it will be allocated and we removed footer for allocated blocks*/
    asize = round_up(size + wsize, dsize);
    /*check to make sure that asize is bigger than the min_block_size*/
    if(asize<min_block_size)
        asize = min_block_size;
  
    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);
    //dbg_printf("malloc end printheap: \n");
    //mm_printheap();
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * <what does free do?>
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    //dbg_printf("free1: ");
    //dbg_printf(" %p\n", block);
    //mm_printheap();

    /*write new header and footer to the block to free it*/
    write_header(block, size, get_prev_alloc(block), false);
    write_footer(block, size, get_prev_alloc(block), false);
    //set_next_prev_alloc(block, false);
    //set_next_prev_alloc_footer(block, false);

    /*set the block's prev and next to null because it is a new free block*/
    block->prev = NULL;
    block->next = NULL;
    //dbg_printf("free2: \n");
    //mm_printheap();
    /*coalesce the new free block*/
    coalesce(block);
    
}

/*
 * realloc: reallocate a given pointer with a given size
 */
void *realloc(void *ptr, size_t size)
{
    //dbg_printf("realloc: \n");
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    //dbg_printf("calloc: \n");
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: extends the heap when there is no free block in heap 
 *     that is big enough to allocate the given size
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    /*write new header and footer for the block*/
    write_header(block, size, get_prev_alloc(block), false);
    write_footer(block, size, get_prev_alloc(block), false);
    /*set its next and prev to null because it's a new free block*/
    block->next = NULL;
    block->prev = NULL;
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, true);
    //dbg_printf("extend heap: \n");
    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * coalesce: combine consecutive free blocks to save memory usage
 */
static block_t *coalesce(block_t * block) 
{
    block_t * next_block = find_next(block);
    bool next_alloc = get_alloc(next_block);
    bool prev_alloc = get_prev_alloc(block);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc) { /* Case 1 */
        //insert the block into freelist and return

        //dbg_printf("Coalecse case 1 start: \n");
        //mm_printheap();

        /*write the prev_alloc bit of the next block before returning*/
        set_next_prev_alloc(block, false);
        //set_next_prev_alloc_footer(block, false);
        /*put the block into freelist*/
        fl_insert(block);
        
        //mm_printfreelist();
        //dbg_printf("Coalecse case 1 end: \n");
        //mm_printheap();
        return block;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
        //remove next block from freelist because it's combined with current block
        //dbg_printf("Coalecse case 2 start: \n");
        //mm_printheap();
        fl_remove(next_block); /* remove next block from freelist */
        size += get_size(next_block); /*add the sizes together*/
        /*write new header and new footer to combine the two blocks*/
        write_header(block, size, true, false);
        write_footer(block, size, true, false);
        /*no need to change the pointer here because the start point does not change*/
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */
        //remove prev block from freelist because it's combined with current block
        //dbg_printf("Coalecse case 3 start: \n");
        //mm_printheap();
        fl_remove(find_prev(block)); /* remove prev block from freelist */
        size += get_size(find_prev(block)); /*add the sizes together*/
        /*write new header and new footer to combine the two blocks*/
        write_footer(block, size, get_prev_alloc(find_prev(block)), false);
        write_header(find_prev(block), size, get_prev_alloc(find_prev(block)), false);
        /*change the start pointer to the prev block*/
        block = find_prev(block);
        
    }
    else { /* Case 4 */
        //remove next and prev block from freelist 
        //  because they are combined with current block
        //dbg_printf("Coalecse case 4 start: \n");
        //mm_printheap();
        fl_remove(next_block); /* remove next block from freelist */
        fl_remove(find_prev(block)); /* remove prev block from freelist */
        size += get_size(find_prev(block)) + get_size(next_block); /* add the total size*/
        /*write the header and the footer to combine the three blocks*/
        write_header(find_prev(block), size, get_prev_alloc(find_prev(block)), false);
        write_footer(next_block, size, get_prev_alloc(find_prev(block)), false);
        /*set the block pointer to the prev block because it starts at prev block now*/
        block = find_prev(block);
        
    }

    /*set the prev_alloc bit of the next block to true*/
    set_next_prev_alloc(block, false);
    //set_next_prev_alloc_footer(block, false);

    /*insert the current block to the freelist*/
    fl_insert(block);
    //dbg_printf("Coalecse case 2-4 end: \n");
    //mm_printheap();
    return block;
}

/*
 * place: place the given size into the given block
 *     check if the remainning is big enough to make a new free block
 *     if it is split the block into two, does not split otherwise.
 */
static void place(block_t *block, size_t asize)
{
    //dbg_printf("Place: \nf");
    //mm_printheap();
    size_t csize = get_size(block);
    //remove block from freelist because it's no longer free
    fl_remove(block);

    //place case 1: split block if the remainning size is bigger than min size
    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        /*only write the header of the block because it is allocated*/
        write_header(block, asize, get_prev_alloc(block), true);
        //write_footer(block, asize, get_prev_alloc(block), true);
        
        /*for the rest block size write footer and write header
            because it is a new free block*/
        block_next = find_next(block);
        write_header(block_next, csize-asize, true, false);
        write_footer(block_next, csize-asize, true, false);

        //set the prev and next in block_next to 0 since it's a new free block
        block_next->prev = 0;
        block_next->next = 0;
        
        //dbg_printf("Place case 1: \n");
        //mm_printheap();
        //set_next_prev_alloc(block, true);

        //coalesce for the new free block and put it in freelist
        coalesce(block_next);
    }
    /*place case 2 when the rest size is smaller than min_block_size
        does not split the block*/
    else
    { 
        /*only write header to the block because it is now allocated*/
        write_header(block, csize, get_prev_alloc(block), true);
        //write_footer(block, csize, get_prev_alloc(block), true);
 
        /*set the next block's prev_alloc to true
            because we do not coalesce here, 
            we need to set it by calling the set_prev function*/
        set_next_prev_alloc(block, true);
        //dbg_printf("Place case 2: \n");
        //mm_printheap();
    }
}

/*
 * find_fit: uses nth fit method to find a fit for the given size
 */
static block_t *find_fit(size_t asize)
{
    //dbg_printf("find_fit start: \n");
    //mm_printheap();
    block_t *block;
    block_t *best_fit=NULL;
    int i = 0;
    //dbg_printf("freelist: \n");
    //mm_printfreelist();

    //use for loop to find the nth fit
    //find the first 50 blocks that fit asize and compare them
    for (block = freelist_start; block != 0 && i<50;
                             block = block->next)
    {
        //if the block size equals asize, it a perfect fit
        //  return immediately
        if (asize == get_size(block))
        {
            return block; 
        //if did not find perfect fit, continue searching 
        }else if(asize < get_size(block)){
            //make the first fit block as the current fit
            if(i==0){
                best_fit = block;
            //everytime we find a fit, compare to the current fit
            //  if the size of current fit is bigger, set the current fit to the new fit
            }else if(get_size(block) < get_size(best_fit)){
                best_fit = block;
            }
            //repeat this step until we search the entire freelist
            //  or we find 50 fits already, then return the current best fit
            i++;
        }
        
    }
    

    return best_fit; // no fit found
}




/* 
 * checks for all the possible invariants in the program
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)  
{ 
    // delete this line; it's a placeholder so that the compiler
    // will not warn you about an unused variable.
    //check if all free blocks are coalesced
    if(!check_freeblock_coalesce()){
        printf("Fail: check free blocks coalesced LINE: %d\n", line);
        return false;
    }

    //check the prev_alloc bit are set correctly
    if(!check_prev_alloc()){
        printf("Fail: check prev alloc LINE: %d\n", line);
        return false;
    }

    //check all the freeblocks are in the freelist
    if(!check_all_freeblocks_in_freelist()){
        printf("Fail: check all free block in freelist LINE: %d\n", line);
        return false;
    }
 
    //check all the blocks are bigger than minimum block size
    if(!check_if_size_smaller_than_minsize()){
        printf("Fail: check if block size is smaller than min block size LINE: %d\n", line);
        return false;
    }

    //check all the freeblocks are linked to each other
    if(!check_freelist_correctly_linked()){
        printf("Fail: check freelist correctly linked LINE: %d\n", line);
        return false;
    }

    //check if the allocated blocks are overlapping
    if(!check_alloc_block_overlap()){
        printf("Fail: check alloc block overlap LINE: %d\n", line);
        return false;
    }

    if(!check_pointer_valid()){
        printf("Fail: check pointers valid LINE: %d\n", line);
        return false;
    }
    return true;
}

//checkheap helper functions
/*
 * mm_printheap: 
 *   print out the entire heap using loop.
 */
void mm_printheap(){
    block_t *b;
    for (b = heap_start; get_size(b) != 0;
		b = find_next(b)) {
	dbg_printf("%p:\tsize: %lu\talloc: %d\tprev_alloc: %d",
		b, get_size(b), get_alloc(b), get_prev_alloc(b));
	if (get_alloc(b)) {
		dbg_printf("\n");
	}
	else {
		dbg_printf("\tprev: %p\tnext: %p\n", b->prev, b->next);
	}
    }
}

/*
 * mm_printfreelist: 
 *   print out the entire freelist using loop.
 */
void mm_printfreelist(){
    block_t *b;
    for (b = freelist_start; b != 0;
		b = b->next) {
	printf("%p:\tsize: %lu\talloc: %d\tprev_alloc: %d",
		b, get_size(b), get_alloc(b), get_prev_alloc(b));
	if (!get_alloc(b)) {
		dbg_printf("\tprev: %p\tnext: %p\n", b->prev, b->next);
	}
    }
}


/*
 * check_freeblock_coalesce: 
 *   loop through heap to check if all the free blocks are
 *   coalesced. Make sure that there is no consecutive free blocks.
 *   return false if find any, true otherwise.
 */
bool check_freeblock_coalesce(){
    block_t *block;
    for (block = heap_start; get_size(block) > 0 && get_size(find_next(block)) > 0;
                             block = find_next(block))
    {

        if (get_alloc(block)==0 && get_alloc(find_next(block))==0)
        {
            return false;  
        }
        
    }
    return true; 
}

/*
 * check_prev_alloc: 
 *   loop through heap to check if all the blocks' prev_alloc are
 *   the same as their prev blocks' alloc.
 *   return false if find any, true otherwise.
 */
bool check_prev_alloc(){
    block_t *block;
    for (block = heap_start; get_size(block) != 0;
                             block = find_next(block))
    {
        if (get_size(find_next(block)) == 0){
            break;
        }else{
            if (get_alloc(block) != get_prev_alloc(find_next(block)))
            {
                dbg_printf("\tprev: %p\tnext: %p\n", find_prev(block), find_next(block));
                return false;  
            }
        }     
    }
    return true;  

}

/*
 * check_all_freeblocks_in_freelist: 
 *   loop through heap to check if 
 *   all the free blocks are in the freelist.
 *   return false if find any, true otherwise.
 */
bool check_all_freeblocks_in_freelist(){
    block_t *b;
    int i = 0;
    int j = 0;
    for (b = heap_start; get_size(b) != 0 && b!=0;
		b = find_next(b)) {
        if(!get_alloc(b)){
            i++;
        }  
    }

    for (b = freelist_start; b!=0 && get_size(b) != 0;
		b = b->next) {
        j++; 
    }

    if(i!=j){
        dbg_printf("free blocks in heap: %d\tfreelist: %d\t", i, j);
        return false;
    }else
        return true;
}

/*
 * check_if_size_smaller_than_minsize: 
 *   loop through heap to check if 
 *   any block has size smaller than the min_block_size.
 *   return false if find any, true otherwise.
 */
bool check_if_size_smaller_than_minsize(){
    block_t *block;
    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (get_size(block)< min_block_size)
        {
            return false;  
        }
        
    }
    return true; 
}

/*
 * check_freelist_correctly_linked: 
 *   print out the entire freelist using loop.
 */
bool check_freelist_correctly_linked(){
    block_t *b;
    block_t *next;
    for (b = freelist_start; b != 0 && b->next != 0;
		b = b->next) {
        next = b->next;
	if (!(b->next==next && next->prev==b)) {
            return false;
	}
    }
    return true;
}

/*
 * check_alloc_block_overlap: 
 *   loop through heap to check if 
 *   all the blocks + its size equals its next block.
 *   return false if find any, true otherwise.
 */
bool check_alloc_block_overlap(){
    block_t *block;
    block_t *next;
    for (block = heap_start; get_size(block) != 0 && find_next(block) != 0;
                             block = find_next(block))
    {
        next = (block_t *)(((char *)block) + get_size(block));
        if ( next != find_next(block))
        {
            return false;  
        }     
    }
    return true;  
}

/*
 * check_pointer_valid: 
 *   loop through heap to check if 
 *   all the blocks' pointers are valid.
 *   return false if find any, true otherwise.
 */
bool check_pointer_valid(){
    block_t *block;
    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {
        if ( (char *)(block->header) == NULL)
            return false;  
        if ( (char *)(block->payload) == NULL)
            return false;
    }
    return true;

}


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool prev_alloc, bool alloc)
{
    /*if prev_alloc is false, only pack the alloc_mask*/
    if(!prev_alloc){
        return (size | alloc_mask);
    }else if(!alloc){   /*if alloc is false, only pack the prev_alloc_mask*/
        return (size | prev_alloc_mask);
    }else if(alloc&&prev_alloc){  /*if both are true, pack both*/
        return (size | prev_alloc_mask | alloc_mask);
    }else    /*if none is true, only return size*/
        return size;

}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    
    if(get_alloc(block))    /*if block is allocated, only leave space for header*/
        return asize-wsize;
    else    /*if block is not allocated, leave space for header and footer*/
        return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * extract_prev_alloc: returns the prev allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_prev_alloc(word_t word)
{
    return (bool)(word & prev_alloc_mask);
}
/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * get_prev_alloc: returns true when the prev block is allocated based on the
 *            block header's second lowest bit, and false otherwise.
 */
static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);

}


/*
 * write_header: given a block and its size, prev_alloc and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_alloc, alloc);
}


/*
 * write_footer: given a block and its size, prev_alloc and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool prev_alloc, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, prev_alloc, alloc);
}

/*
 * set_next_prev_alloc: given a block and its allocation status,
 *               writes an appropriate value to the next block header.
 */
static void set_next_prev_alloc(block_t *block, bool prev_alloc){
    block = find_next(block);
    block->header = pack(get_size(block), prev_alloc, get_alloc(block));
    /*if the block is free, also set prev_alloc in its footer*/
    if(!get_alloc(block))
        write_footer(block, get_size(block), prev_alloc, get_alloc(block));
}

/*
 * set_next_prev_alloc_footer: given a block and its prev allocation status,
 *               writes an appropriate value to the next block footer.
 */
static void set_next_prev_alloc_footer(block_t *block, bool prev_alloc){
    block = find_next(block);
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(get_size(block), prev_alloc, get_alloc(block));
}
/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
