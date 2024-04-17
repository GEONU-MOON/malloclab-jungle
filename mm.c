/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team9",
    /* First member's full name */
    "moon",
    /* First member's email address */
    "moon@jungle.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE 4 // 워드 = 헤더 = 풋터 사이즈(bytes)
#define DSIZE 8 // 더블워드 사이즈(bytes)
#define CHUNKSIZE (1 << 12) // heap을 이정도 늘린다(bytes)
#define LISTLIMIT 20 //list의 limit 값을 설정해준다. CHUNKSIZE에 비해 충분히 큰 값을 준 것 같다(정확한 이유 모르겠음)

#define MAX(x, y) ((x) > (y)? (x):(y))
// pack a size and allocated bit into a word 
#define PACK(size, alloc) ((size) | (alloc))

// Read and wirte a word at address p
//p는 (void*)포인터이며, 이것은 직접 역참조할 수 없다.
#define GET(p)     (*(unsigned int *)(p)) //p가 가리키는 놈의 값을 가져온다
#define PUT(p,val) (*(unsigned int *)(p) = (val)) //p가 가리키는 포인터에 val을 넣는다

// Read the size and allocated fields from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7) // ~0x00000111 -> 0x11111000(얘와 and연산하면 size나옴)
#define GET_ALLOC(p) (GET(p) & 0x1)  // 할당이면 1, 가용이면 0

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //헤더+데이터+풋터 -(헤더+풋터)

// 현재 bp에서 WSIZE를 빼서 header를 가리키게 하고, header에서 get size를 한다.
// 그럼 현재 블록 크기를 return하고(헤더+데이터+풋터), 그걸 현재 bp에 더하면 next_bp나옴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_FREE(bp) (*(void**)(bp))
#define SUCC_FREE(bp) (*(void**)(bp + WSIZE))


static void *heap_listp;          
static void *segregation_list[LISTLIMIT];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_block(void *bp);
static void insert_block(void *bp, size_t size);

/*
 * 함수: int mm_init(void)
 * -------------------------
 * 메모리 매니저 초기화 함수.
 * 
 * 반환값:
 *     - 0: 성공
 *     - -1: 실패
 * 
 * 이 함수는 segregated 방식으로 메모리를 관리하기 위한 초기화 작업을 수행.
 * 먼저 segregated 리스트를 NULL로 초기화.
 * 그런 다음, 초기 힙 영역을 할당.
 * 힙 영역이 할당되지 않으면 -1을 반환.
 * 초기 힙에는 프롤로그 블록, 에필로그 블록, 그리고 두 개의 할당 가능한 블록이 생성.
 * 프롤로그 블록과 에필로그 블록은 메모리 할당 영역의 시작과 끝을 표시.
 * 그리고 초기 힙을 확장하여 추가적인 메모리가 필요한 경우 확장.
 * 힙 확장이 실패하면 -1을 반환.
 * 모든 초기화 작업이 성공적으로 완료되면 0을 반환.
 */
int mm_init(void)
{
    int list;

    for (list = 0; list < LISTLIMIT; list++) {
        segregation_list[list] = NULL;     
    }                                      
    
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                            
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); 
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); 
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     
    heap_listp = heap_listp + 2*WSIZE;  

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/*
 * 함수: void *mm_malloc(size_t size)
 * -----------------------------------
 * 메모리 할당 함수.
 * 
 * 매개변수:
 *     - size: 할당하려는 메모리의 크기
 * 
 * 반환값:
 *     - 할당된 메모리 블록의 포인터
 *     - 실패할 경우 NULL
 * 
 * 이 함수는 요청된 크기에 따라 메모리를 할당.
 * 먼저 요청된 크기를 정렬하고 헤더와 풋터 크기를 추가하여 할당 가능한 블록의 크기를 계산.
 * 할당 가능한 블록을 찾을 수 있는지 확인하고, 찾을 수 있다면 해당 블록에 메모리를 할당하고 반환.
 * 할당 가능한 블록을 찾을 수 없다면, 추가적인 메모리를 할당하기 위해 힙을 확장.
 * 힙 확장이 실패하면 NULL을 반환하고, 성공하면 새로운 블록에 메모리를 할당하고 반환.
 */
void *mm_malloc(size_t size)
{
    int asize = ALIGN(size + SIZE_T_SIZE);

    size_t extendsize; 
    char *bp;

    if ((bp = find_fit(asize)) != NULL) 
    {
        place(bp, asize);               
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * 함수: void mm_free(void *ptr)
 * -------------------------------
 * 메모리 해제 함수.
 * 
 * 매개변수:
 *     - ptr: 해제할 메모리 블록의 포인터
 * 
 * 이 함수는 주어진 포인터가 가리키는 메모리 블록을 해제.
 * 먼저 해제할 블록의 크기를 가져온 후, 헤더와 풋터를 각각 해제 상태로 설정.
 * 그런 다음, 병합 함수를 호출하여 연속된 빈 블록들을 병합.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * 함수: void *mm_realloc(void *ptr, size_t size)
 * -----------------------------------------------
 * 메모리 재할당 함수.
 * 
 * 매개변수:
 *     - ptr: 재할당할 메모리 블록의 포인터
 *     - size: 새로운 메모리 블록의 크기
 * 
 * 반환값:
 *     - 새로 할당된 메모리 블록의 포인터
 *     - 실패할 경우 NULL
 * 
 * 이 함수는 주어진 포인터가 가리키는 메모리 블록의 크기를 변경.
 * 우선 새로운 크기에 맞게 메모리를 할당하고, 할당에 실패한 경우 NULL을 반환.
 * 그런 다음, 이전 메모리 블록의 크기를 가져와서 새로운 크기와 비교하여 복사할 크기를 결정.
 * 복사할 크기만큼 메모리를 복사한 후, 이전 메모리 블록을 해제.
 * 마지막으로 새로 할당된 메모리 블록의 포인터를 반환.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * 함수: static void *extend_heap(size_t words)
 * ---------------------------------------------
 * 힙을 확장하는 함수.
 * 
 * 매개변수:
 *     - words: 확장할 워드 수
 * 
 * 반환값:
 *     - 확장된 힙 영역의 시작 주소
 *     - 실패할 경우 NULL
 * 
 * 이 함수는 힙 영역을 확장하여 추가적인 메모리를 할당.
 * 확장할 크기는 요청된 워드 수를 기반으로 결정되며, 홀수 개의 워드는 짝수 개로 조정.
 * 힙 영역을 확장하는데 실패하면 NULL을 반환.
 * 성공한 경우에는 새로운 블록의 헤더와 풋터를 설정하고, 뒤따라오는 블록의 헤더를 설정하여 메모리의 끝을 표시.
 * 그런 다음, 병합 함수를 호출하여 연속된 빈 블록들을 병합.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));        
    PUT(FTRP(bp), PACK(size, 0));        
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

    return coalesce(bp);
}

/*
 * 함수: static void *coalesce(void *bp)
 * ---------------------------------------
 * 빈 메모리 블록들을 병합하는 함수입니다.
 * 
 * 매개변수:
 *     - bp: 병합할 메모리 블록의 포인터
 * 
 * 반환값:
 *     - 병합된 메모리 블록의 포인터
 * 
 * 이 함수는 빈 메모리 블록들을 병합하여 하나의 큰 메모리 블록으로 만든다.
 * 주어진 메모리 블록 주변의 블록들의 할당 상태를 확인하여 병합 가능한지 판단.
 * 이전 블록과 다음 블록이 모두 할당되어 있으면, 현재 블록을 삽입하고 반환.
 * 이전 블록이 할당되어 있고 다음 블록이 빈 상태이면, 다음 블록을 제거하고 크기를 합친 후 현재 블록을 반환.
 * 이전 블록이 빈 상태이고 다음 블록이 할당되어 있으면, 이전 블록을 제거하고 크기를 합친 후 이전 블록의 포인터를 반환.
 * 이전 블록과 다음 블록이 모두 빈 상태이면, 두 블록을 모두 제거하고 크기를 합친 후 이전 블록의 포인터를 반환.
 * 모든 병합이 완료되면 새로운 블록을 삽입한 후 그 포인터를 반환.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        insert_block(bp,size);      
        return bp;
    }
    else if (prev_alloc && !next_alloc) 
    {
        remove_block(NEXT_BLKP(bp)); 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        remove_block(PREV_BLKP(bp)); 
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) 
    {
        remove_block(PREV_BLKP(bp)); 
        remove_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp); 
    }

    insert_block(bp, size); 
    return bp;
}

/*
 * 함수: static void place(void *bp, size_t asize)
 * ----------------------------------------------
 * 메모리를 할당하는 함수.
 * 
 * 매개변수:
 *     - bp: 할당할 메모리 블록의 포인터
 *     - asize: 할당하려는 메모리 블록의 크기
 * 
 * 이 함수는 주어진 메모리 블록에 메모리를 할당.
 * 먼저 해당 블록을 리스트에서 제거.
 * 할당된 블록의 크기에서 요청된 크기를 뺀 값이 최소 할당 가능 크기보다 큰지 확인.
 * 만약 그렇다면, 블록을 나누어 사용할 수 있음.
 * 블록을 분할하고 할당된 부분과 빈 부분의 헤더와 풋터를 설정한 후, 나머지 빈 부분을 병합.
 * 그렇지 않다면, 블록 전체를 할당하고 헤더와 풋터를 설정.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);

    if ((csize - asize) >= (2 * DSIZE)) 
    {   
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); 
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp); 
    }                 
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * 함수: static void *find_fit(size_t asize)
 * -----------------------------------------
 * 할당 가능한 빈 메모리 블록을 찾는 함수.
 * 
 * 매개변수:
 *     - asize: 찾고자 하는 메모리 블록의 크기
 * 
 * 반환값:
 *     - 할당 가능한 빈 메모리 블록의 포인터
 *     - 찾지 못한 경우 NULL
 * 
 * 이 함수는 요청된 크기보다 크거나 같은 빈 메모리 블록을 찾아 반환.
 * 먼저 요청된 크기를 기준으로 검색을 시작하고, 리스트의 각 요소를 순회하면서 적절한 블록을 찾음.
 * 검색을 시작하는 리스트는 요청된 크기를 가진 가장 가까운 리스트이며, 리스트가 빈 경우 더 작은 리스트로 이동.
 * 적절한 블록을 찾으면 해당 블록의 포인터를 반환하고, 찾지 못한 경우 NULL을 반환.
 */
static void *find_fit(size_t asize)
{
    void *bp;

    int list = 0;
    size_t searchsize = asize;

    while (list < LISTLIMIT){
        if ((list == LISTLIMIT-1) || (searchsize <= 1)&&(segregation_list[list] != NULL)){
            bp = segregation_list[list];

            while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))){
                bp = SUCC_FREE(bp);
            }
            if (bp != NULL){
                return bp;
            }
        }
        searchsize >>= 1;
        list++;
    }

    return NULL; 
}

/*
 * 함수: static void remove_block(void *bp)
 * ----------------------------------------
 * 리스트에서 블록을 제거하는 함수.
 * 
 * 매개변수:
 *     - bp: 제거할 블록의 포인터
 * 
 * 이 함수는 주어진 블록을 리스트에서 제거.
 * 먼저 제거할 블록의 크기를 가져온 후, 해당 블록이 속한 리스트의 인덱스를 결정.
 * 리스트의 인덱스는 블록의 크기를 기반으로 계산됨.
 * 제거할 블록의 선행자와 후속자를 확인하여 포인터를 업데이트하고,
 * 리스트에서 블록을 제거한 후 적절한 포인터를 설정.
 */
static void remove_block(void *bp){
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (SUCC_FREE(bp) != NULL){ 
        if (PRED_FREE(bp) != NULL){
            PRED_FREE(SUCC_FREE(bp)) = PRED_FREE(bp);
            SUCC_FREE(PRED_FREE(bp)) = SUCC_FREE(bp);
        }else{
            PRED_FREE(SUCC_FREE(bp)) = NULL;
            segregation_list[list] = SUCC_FREE(bp);
        }
    }else{ 
        if (PRED_FREE(bp) != NULL){ 
            SUCC_FREE(PRED_FREE(bp)) = NULL;
        }else{ 
            segregation_list[list] = NULL;
        }
    }
    return;
}

/*
 * 함수: static void insert_block(void *bp, size_t size)
 * -----------------------------------------------------
 * 리스트에 블록을 삽입하는 함수.
 * 
 * 매개변수:
 *     - bp: 삽입할 블록의 포인터
 *     - size: 삽입할 블록의 크기
 * 
 * 이 함수는 주어진 블록을 리스트에 삽입.
 * 먼저 삽입할 블록의 크기를 기반으로 리스트의 인덱스를 결정.
 * 리스트의 인덱스는 블록의 크기를 기반으로 계산.
 * 그런 다음, 리스트에서 올바른 위치를 찾을 때까지 순회하고 삽입할 위치를 결정.
 * 올바른 위치를 찾았을 때, 블록을 삽입하고 연결된 포인터를 업데이트.
 * 블록이 리스트의 처음에 삽입되는 경우, 적절한 포인터를 설정하여 리스트의 시작을 업데이트.
 */
static void insert_block(void *bp, size_t size){
    int list = 0;
    void *search_ptr;
    void *insert_ptr = NULL; 

    while ((list < LISTLIMIT - 1) && (size > 1)){
        size >>=1;
        list++;
    }

    search_ptr = segregation_list[list];

    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))){
        insert_ptr = search_ptr;
        search_ptr = SUCC_FREE(search_ptr); 
    }

    if (search_ptr != NULL){ 
        if (insert_ptr != NULL){ 
            SUCC_FREE(bp) = search_ptr; 
            PRED_FREE(bp) = insert_ptr;
            PRED_FREE(search_ptr) = bp;
            SUCC_FREE(insert_ptr) = bp;
        }else{ 
            SUCC_FREE(bp) = search_ptr;
            PRED_FREE(bp) = NULL;
            PRED_FREE(search_ptr) = bp;
            segregation_list[list] = bp; 
        }
    }else{ 
        if (insert_ptr != NULL){        
            SUCC_FREE(bp) = NULL;       
            PRED_FREE(bp) = insert_ptr; 
            SUCC_FREE(insert_ptr) = bp;
        }else{ 
            SUCC_FREE(bp) = NULL;
            PRED_FREE(bp) = NULL;
            segregation_list[list] = bp; 
        }
    }
    return;
}