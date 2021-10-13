/*
Author: Chang Hi Lee(lee.c@wustl.edu)
Name: mm.c
Function: 64-bit struct-based implicit free list memory allocator that implements malloc, free, and realloc along with supporting functions
Description: My allocator maintains two pointers to a free list only when the block is freed. When the block is allocated, the pointers will be overwritten and thus lose their freed status. This is managed by helper functions in list adding and removing.
****** 
Structure of free and allocated blocks: 
A block variable is a union composed of a payload and two pointers to a free list.
*          When the block is freed, it will have a header and a footer, and the two free list pointers will override the payload.
*          When the block is allocated, it will only have a header and the payload will override the two pointers.
Organization of the free list: The free lists are segregated free lists with user-defined categories. Nth fitting is performed also with user-defined variables.
******
 */

/* Do not change the following! */

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
// #define DEBUG // uncomment this line to enable debugging

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
	union //annonymous union
	{
		struct //annonymous struct
		{
			struct block* free_prev;
			struct block* free_next;
		};
		char payload[0];
		/*
		 * We can't declare the footer as part of the struct, since its starting
		 * position is unknown
		 */
	};
} block_t;


/* Global variables */
static block_t *heap_start = NULL; //Pointer to first block

static block_t* heap_prol = NULL; //Pointers to heap prologue and epilogue
static block_t* heap_epil = NULL; 

static int seg_num = 3; //number of segregated lists
static int first_list = 0;
static int second_list = 1;
static int third_list = 2;
static block_t* all_free_list_start[3] = {NULL}; //Array of pointers to free list start and end blocks. The number inside brackets should match seg_num.
static block_t* all_free_list_end[3] = {NULL};

static const size_t cat1 = 4*sizeof(word_t); //first size category: 32 bytes
static const size_t cat2 =4*sizeof(word_t) * 1.5; //second size category: 64 - 96 bytes
static const size_t cat3 = 4*sizeof(word_t) * 2; //third size category: 96 bytes and above

//static block_t* free_list_start_arr[] = { free_list1_start, free_list2_start, free_list3_start }; //array of pointers to segregated free lists' start and end blocks
//static block_t* free_list_end_arr[] = { free_list1_end, free_list2_end, free_list3_end };


static int N = 20; //global variable for Nth fit in find_fit

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void list_add(block_t* block, block_t* free_list_start, block_t* free_list_end, int ind);
static void list_rem(block_t* block, block_t* free_list_start, block_t* free_list_end, int ind);
static void add_to_free_list(block_t* block);
static void rem_from_free_list(block_t* block);
static void clear_free_list();

/*
 * mm_init: creates a new, empty heap, and resets all global variables.
 */
bool mm_init(void) 
{
	//reset global variables
	heap_start = NULL;
	heap_prol = NULL;
	heap_epil = NULL;
	clear_free_list();

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true);
    start[1] = pack(0, true);

    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
	heap_prol = (block_t*) & (start[0]);
	heap_epil = heap_start;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc: requests memory from the heap to be allocated and returns a pointer to the start address of the memory. 
 *              If the heap needs more memory, the heap is extended.
 */
void *malloc(size_t size) 
{
    //dbg_ensures(mm_checkheap(__LINE__));
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
        //dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

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
    //dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * free: rewrites header and footer of the block to indicate the block is free, coalesces the block, than adds to global free list
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);
	add_to_free_list(block); //add freed block to the global free list

    coalesce(block);
}

/*
 * realloc: reallocates the memory previously allocated by the call to malloc
 */
void *realloc(void *ptr, size_t size)
{
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
 * calloc: allocates memory for an array of elements with corresponding size and initializes all bytes in the allocated storage to zero.
 */
void *calloc(size_t elements, size_t size)
{
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

/******** Helper and debug routines ********/

/*
 * extend_heap: requests additional memory for the heap. The free block is the legal size of a block that can contain length "size".
 * Then, it creates the free block header/footer, the new epilogue header, and coalesces the free block.
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

	heap_epil = (block_t*)((char*)heap_epil + size);

    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
	add_to_free_list(block); // Add freed block to global free list

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * coalesce: combines any adjacent free blocks into one large free block.
 */
static block_t *coalesce(block_t * block) 
{
	// first check that the block itself isn't allocated
	if (get_alloc(block))
	{
		return block;
	}

	block_t* coa_block = NULL; //the coalesced block to return
	word_t* block_prev_footer = find_prev_footer(block);
	word_t* block_next_header = (word_t*)((char*)block + get_size(block));

	bool alloc_prev = extract_alloc(*block_prev_footer);
	bool alloc_next = extract_alloc(*block_next_header);

	//if both prev and next blocks are free, get block positions
	if (!alloc_prev && !alloc_next) //if previous and next blocks are unallocated and within the heap
	{
		block_t* block_prev = find_prev(block);
		block_t* block_next = find_next(block);
		size_t size_total = get_size(block) + get_size(block_prev) + get_size(block_next);

		//remove blocks to be coalesced from global free list
		rem_from_free_list(block_prev);
		rem_from_free_list(block_next);
		rem_from_free_list(block);

		write_header(block_prev, size_total, false);
		write_footer(block_next, size_total, false);
		coa_block = block_prev;
	}

	//if only next block is free, get next block position
	if (alloc_prev && !alloc_next)
	{
		block_t* block_next = find_next(block);
		size_t size_total = get_size(block) + get_size(block_next);

		rem_from_free_list(block_next);
		rem_from_free_list(block);

		write_header(block, size_total, false);
		write_footer(block_next, size_total, false);
		coa_block = block;
	}

	//if only prev block is free, get prev block location
	if (!alloc_prev && alloc_next) 
	{
		block_t* block_prev = find_prev(block);
		size_t size_total = get_size(block) + get_size(block_prev);

		rem_from_free_list(block_prev);
		rem_from_free_list(block);

		write_header(block_prev, size_total, false);
		write_footer(block, size_total, false);
		coa_block = block_prev;
	}

	//if both prev and next blocks are allocated
	if (alloc_prev && alloc_next)
	{
		coa_block = block;
		rem_from_free_list(block);
	}

	add_to_free_list(coa_block); //add coalesced block back to the global free list
	return coa_block;
}

/*
 * place:  modifies the free block to be read as allocated by writing the block header to "true"
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size) // "block" = block to place the data into, asize = adjusted size of requested memory
    {
        block_t *block_next;
		rem_from_free_list(block);
        write_header(block, asize, true);
        write_footer(block, asize, true);
        
        //if another block can fit in the remaining space, perform splitting
        block_next = find_next(block); //next block is the block after the size of current block has been traversed in the heap
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
		add_to_free_list(block_next);
    }

    else
    { 
		rem_from_free_list(block);
        write_header(block, csize, true);
        write_footer(block, csize, true);
    }
}

/*
 * find_fit: searches through the entire free lists to find a suitable empty block that can fit the new data with size "asize".
 */
static block_t *find_fit(size_t asize)
{
    block_t* free_list_start = NULL;
    if (asize >= cat1 && asize < cat2)
    {
        free_list_start = all_free_list_start[first_list];
        if (free_list_start == NULL)
        {
            free_list_start = all_free_list_start[second_list];
            if(free_list_start == NULL)
            {
                free_list_start = all_free_list_start[third_list];     
			}
		}
	}

    if (asize  >= cat2 && asize < cat3) //if block is between 48 and 96 bytes
    {
        free_list_start = all_free_list_start[second_list];
         if (free_list_start == NULL)
        {
            free_list_start = all_free_list_start[third_list];
        }
	}

    if (asize  >= cat3) //if block is larger than 96 bytes
    {
        free_list_start = all_free_list_start[third_list];
	}

	if (free_list_start == NULL) //if there are no free blocks
	{
		return NULL;
	}

	block_t* free_block = free_list_start;
	int i = 0;
	size_t min_diff = mem_heapsize();
	block_t* min_block = NULL; //if no fit is found, min_block will remain NULL
	while (free_block != NULL && i <= N) //perform Nth fitting with global variable
	{
		if (asize <= get_size(free_block))
		{
			if (get_size(free_block) - asize < min_diff)
			{
				min_diff = get_size(free_block) - asize;
				min_block = free_block;
			}
		}

		free_block = free_block->free_next;
		i++;
	}

    return min_block; 
}

/* 
 * mm_checkheap: iterates through the entire heap and checks that
 * 1. all headers and footers match for free blocks
 * 2. all blocks are within heap range
 * 3. there are no two contiguous free blocks
 * 4. all blocks in the free list are unallocated
 */
bool mm_checkheap(int line)  
{ 
    block_t* cur_block = heap_start;
  
	for (cur_block = heap_start; get_size(cur_block) > 0; cur_block = find_next(cur_block))
    {
        //check if all blocks are within heap range
		if (cur_block < heap_prol || cur_block > heap_epil)
		{
			return false;
		}

		//check that there are no two contiguous free blocks
		bool cur_alloc = get_alloc(cur_block);
		bool next_alloc = get_alloc(find_next(cur_block));
		if (!cur_alloc && !next_alloc) //if current and next blocks are both free
		{
			return false;
		}
      
		//check that all blocks in the free list are unallocated
        int i;
        for (i = 0; i < seg_num; i++)
        {
            block_t* free_block = all_free_list_start[i];
		    while (free_block != NULL)
		    {
		    	if (get_alloc(free_block))
		    	{
		    		return false;
		    	}
		    	
                //check if headers and footers match for all free blocks
		        word_t cur_header = free_block->header;
		        word_t cur_footer = *(((word_t*)((char*)free_block + get_size(free_block))) - 1);
		        if (cur_header != cur_footer)
		        {
		        	return false;
		        }

		    	free_block = free_block->free_next;
		    }
		}
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
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
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
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
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
	block_t* block_prev = (block_t*)((char*)block - size);

    return block_prev;
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

/*
 * list_add: given a block to be free, pointers to a free list, and the index of the array of free list pointers, 
 *                adds the block to the free list and updates the global array variable
 */
static void list_add(block_t* block, block_t* free_list_start, block_t* free_list_end, int ind)
{
    //assert(ind < seg_num);
	if (block == NULL || get_alloc(block))
	{
		return;
	}

	if (free_list_start == NULL) //if the free list is empty, insert at root of global free list(LIFO)
	{
		free_list_start = block;
		free_list_end = block;
		block->free_prev = NULL;
		block->free_next = NULL;
	}

	else
	{
		block->free_next = free_list_start;
		block->free_prev = NULL;
		free_list_start->free_prev = block;
		free_list_start = block;
	}

    all_free_list_start[ind] = free_list_start;
    all_free_list_end[ind] = free_list_end;
}

/*
 * list_rem: given a block to be allocated, pointers to a free list, and the index of the array of free list pointers, 
 *                removes the block from the free list and updates the global array variable
 */
static void list_rem(block_t* block, block_t* free_list_start, block_t* free_list_end, int ind)
{
    //assert(ind < seg_num);
    if (block == NULL || get_alloc(block) || free_list_start == NULL)
	{
		return;
	}

	if (free_list_start == free_list_end) //if there is only one free block
	{
		free_list_start = NULL;
		free_list_end = NULL;
	}

	else
	{
		if (block == free_list_start) //if removed block is the start of the free list
		{
			free_list_start = block->free_next;
			free_list_start->free_prev = NULL;
		}

		else if (block == free_list_end) //if removed block is the end of the free list
		{
			free_list_end = block->free_prev;
			free_list_end->free_next = NULL;
		}

		else
		{
			block->free_next->free_prev = block->free_prev;
			block->free_prev->free_next = block->free_next;
		}
	}

	block->free_prev = NULL;
	block->free_next = NULL;

    all_free_list_start[ind] = free_list_start;
    all_free_list_end[ind] = free_list_end;
}

/*
 * add_to_free_list: calls list_add according to the size of the block to be added to a free list
 */
static void add_to_free_list(block_t* block) //adds a newly freed block to the global segmented free lists
{
    size_t block_size = get_size(block);
    if (block_size >= cat1 && block_size < cat2) //if block is the smallest size 
    {
        list_add(block, all_free_list_start[first_list], all_free_list_end[first_list], first_list);
	}

    if (block_size  >= cat2 && block_size < cat3) //if block is between 48 and 96 bytes
    {
        list_add(block, all_free_list_start[second_list], all_free_list_end[second_list], second_list);
	}

    if (block_size  >= cat3) //if block is larger than 96 bytes
    {
        list_add(block, all_free_list_start[third_list], all_free_list_end[third_list], third_list);
	}
}

/*
 * rem_from_free_list: calls list_rem according to the size of the block to be removed from a free list
 */
static void rem_from_free_list(block_t* block) //removes allocated block from global free list
{
    size_t block_size = get_size(block);

    if (block_size >= cat1 && block_size < cat2) //if block is the smallest size 
    {
        list_rem(block,all_free_list_start[first_list], all_free_list_end[first_list], first_list);
	}

    if (block_size  >= cat2 && block_size < cat3) //if block is between 48 and 96 bytes
    {
        list_rem(block, all_free_list_start[second_list], all_free_list_end[second_list], second_list);
	}

    if (block_size  >= cat3) //if block is larger than 96 bytes
    {
        list_rem(block, all_free_list_start[third_list], all_free_list_end[third_list], third_list);
	}
}

/*
 * clear_free_list: on calling mm_init, clears all the segregated free lists so that they are empty
 */
static void clear_free_list()
{
    if (all_free_list_start[first_list] == NULL && all_free_list_start[second_list] == NULL && all_free_list_start[third_list] == NULL)
    {
        return;
	}

    int i;
    for (i = 0; i < seg_num; i++)
    {
        block_t* free_block;
	    for (free_block = all_free_list_start[i]; free_block != NULL; free_block = free_block->free_next)
	    {
	    	rem_from_free_list(free_block);
	    }
	}
}
