#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "Week05_team9",
    "Geonu Moon",
    "moondy220965@gmail.com",
    "",
    ""
};

#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* 기본 상수 & 매크로 */
#define WSIZE 4             // word size
#define DSIZE 8             // double word size
#define CHUNKSIZE (1 << 12) // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)

/* 가용 리스트를 접근/순회하는 데 사용할 매크로 */
#define MAX(x, y) (x > y ? x : y)
#define PACK(size, alloc) (size | alloc)                              // size와 할당 비트를 결합, header와 footer에 저장할 값
#define GET(p) (*(unsigned int *)(p))                                 // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))      // p에 val 저장
#define GET_SIZE(p) (GET(p) & ~0x7)                                   // 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_ALLOC(p) (GET(p) & 0x1)                                   // 할당 상태
#define HDRP(bp) ((char *)(bp)-WSIZE)                                 // Header 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)          // Footer 포인터 (🚨Header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 Footer가 반환됨에 유의)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 포인터

/*
prev/next 블록이 가리키는 곳으로 가는 이중포인터, void*의 값에 *접근함

SUCC(bp): 이 매크로는 현재 가용 블록의 주소를 인자로 받아서 그 블록의 다음 가용 블록의 주소를 반환.
가용 리스트에서 각 블록은 다음 가용 블록을 가리키는 포인터를 가진다.
이 매크로는 현재 블록의 주소에서 WSIZE (워드 크기)만큼 떨어진 곳에 있는 값을 가져온다.
이 값은 다음 가용 블록의 주소를 나타낸다.

PRED(bp): 이 매크로는 현재 가용 블록의 주소를 인자로 받아서 그 블록의 이전 가용 블록의 주소를 반환.
가용 리스트에서 각 블록은 이전 가용 블록을 가리키는 포인터를 가지고 있는다.
이 매크로는 현재 블록의 주소에서 바로 값을 가져온다.
이 값은 이전 가용 블록의 주소를 나타낸다.
*/
#define PRED_FREEP(bp) (*(void* *)(bp))                  // bp 블록이 가리키는 포인터의 값, 즉 bp의 이전 가용 블록의 주소를 가져옴
#define SUCC_FREEP(bp) (*(void* *)(bp + WSIZE))          // bp 블록이 가리키는 포인터의 값, 즉 bp의 다음 가용 블록의 주소를 가져옴

static char *heap_listp; // 힙 시작 포인터 
static char *free_listp; // free 시작 포인터 

int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void *mm_realloc(void *bp, size_t size);
void mm_free(void *bp);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void removeBlock(void *bp);
void putFreeBlock(void *bp);

int mm_init(void) {
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void*) - 1) {
        return -1;
    }
    PUT(heap_listp, 0);                                // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), NULL);               // 이전 가용 블록의 주소
    PUT(heap_listp + (3 * WSIZE), NULL);               // 다음 가용 블록의 주소
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         // 에필로그 Header: 프로s그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄
   
    free_listp = heap_listp + (2 * WSIZE); // free_listp를 PRED 포인터 가리키게 초기화

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    size_t asize; //할당할 블록 사이즈
    size_t extendsize;
    void *bp; 

    if(size <= 0) 
        return NULL;
    
    if(size <= DSIZE) // size가 8byte보다 작다면,
        asize = 2 * DSIZE; // 최소블록조건인 16byte로 맞춤
    else              // size가 8byte보다 크다면
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    //Search the free list for a fit - 적절한 가용(free)블록을 가용리스트에서 검색
    if((bp = find_fit(asize))!=NULL){
        place(bp,asize); //가능하면 초과부분 분할
        return bp;
    }

    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp,asize);
    return bp;
}

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// coalesce 함수: 주어진 가용 블록 주변에 있는 다른 가용 블록을 통합하고 분할하여 필요한 경우 가용 리스트에 추가함
static void *coalesce(void *bp) {
    // 이전 블록과 다음 블록이 할당되었는지 여부 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록이 할당되었는지 여부 (0 or 1)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록이 할당되었는지 여부 (0 or 1)
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    // Case 1: 이전 블록과 다음 블록이 모두 할당되어 있을 때
    if (prev_alloc && next_alloc)
    {
        // 아무 처리도 하지 않음
    }
    // Case 2: 다음 블록이 가용 상태일 때
    else if (prev_alloc && !next_alloc){
        // 다음 블록을 가용 리스트에서 제거
        removeBlock(NEXT_BLKP(bp)); 
        // 현재 블록과 다음 블록을 통합하여 하나의 큰 가용 블록으로 만듦
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0)); // 헤더 업데이트
        PUT(FTRP(bp), PACK(size,0)); // 푸터 업데이트
    }
    // Case 3: 이전 블록이 가용 상태일 때
    else if(!prev_alloc && next_alloc){
        // 이전 블록을 가용 리스트에서 제거
        removeBlock(PREV_BLKP(bp));
        // 이전 블록과 현재 블록을 통합하여 하나의 큰 가용 블록으로 만듦
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp); // bp를 이전 블록으로 업데이트
        PUT(HDRP(bp), PACK(size,0)); // 헤더 업데이트
        PUT(FTRP(bp), PACK(size,0)); // 푸터 업데이트
    }
    // Case 4: 이전 블록과 다음 블록이 모두 가용 상태일 때
    else {
        // 이전 블록과 다음 블록을 가용 리스트에서 제거
        removeBlock(PREV_BLKP(bp)); 
        removeBlock(NEXT_BLKP(bp));
        // 이전 블록과 다음 블록을 통합하여 하나의 큰 가용 블록으로 만듦
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp); // bp를 이전 블록으로 업데이트
        PUT(HDRP(bp), PACK(size, 0)); // 헤더 업데이트
        PUT(FTRP(bp), PACK(size, 0)); // 푸터 업데이트
    }
    putFreeBlock(bp); // 가용 리스트에 연결된 가용 블록 추가

    return bp; // 연결된 가용 블록의 주소 반환
}


void *mm_realloc(void *ptr, size_t size) {
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
함수가 시작되면 먼저 bp라는 포인터를 선언 
이를 free_listp로 초기화. 
free_listp는 가용 리스트의 시작 지점을 나타낸다.

그런 다음, bp가 가리키는 블록이 할당되지 않은 동안(GET_ALLOC(HDRP(bp)) != 1) 가용 리스트를 순회.

각 블록에 대해 크기를 확인하고(GET_SIZE(HDRP(bp)) >= asize), 
요청한 크기보다 크거나 같은 경우 해당 블록을 반환. 
이는 가용한 블록을 찾은 것을 의미.

가용 리스트를 모두 확인한 후에도 적절한 크기의 가용 블록을 찾지 못하면 NULL을 반환.
*/
static void *find_fit(size_t asize) {
    void *bp;
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
    }
    return NULL; 
}

// place 함수: 새로운 할당 블록을 메모리에 배치하고, 필요한 경우에는 남은 공간을 분할하여 가용 블록으로 만듦
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 가져옴
    // 할당된 블록은 가용 리스트에서 제거함
    removeBlock(bp);
    // 남은 공간이 분할할 만큼 충분하면 분할 수행
    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize,1)); // 새로운 할당 블록의 헤더 업데이트
        PUT(FTRP(bp), PACK(asize,1)); // 새로운 할당 블록의 푸터 업데이트
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize-asize,0)); // 남은 공간의 헤더 업데이트
        PUT(FTRP(bp), PACK(csize-asize,0)); // 남은 공간의 푸터 업데이트
        putFreeBlock(bp); // 분할된 블록을 가용 리스트에 추가함
    }
    // 남은 공간이 분할할 만큼 충분하지 않으면 그대로 사용
    else{
        PUT(HDRP(bp), PACK(csize,1)); // 현재 블록을 헤더에 할당 표시로 업데이트
        PUT(FTRP(bp), PACK(csize,1)); // 현재 블록을 푸터에 할당 표시로 업데이트
    }
}

// LIFO 방식으로 새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가
void putFreeBlock(void *bp){
    // 새로운 가용 블록의 다음 가용 블록 포인터를 현재의 가용 리스트 헤드로 설정
    SUCC_FREEP(bp) = free_listp;
    // 새로운 가용 블록의 이전 가용 블록 포인터를 NULL로 설정 (새로운 가용 리스트 헤드이므로 이전 블록이 없음)
    PRED_FREEP(bp) = NULL;
    // 현재의 가용 리스트 헤드인 free_listp의 이전 가용 블록 포인터를 새로운 가용 블록으로 설정
    PRED_FREEP(free_listp) = bp;
    // 새로운 가용 블록을 가용 리스트의 새로운 헤드로 설정
    free_listp = bp;
}

// free list 맨 앞에 프롤로그 블록이 존재
void removeBlock(void *bp){
    // 첫 번째 블록을 없앨 때
    if(bp == free_listp){
        // bp 다음에 오는 블록의 이전 블록 포인터를 NULL로 설정하여 연결을 끊음
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;
        // bp를 제거하고 나면 bp 다음에 오는 블록이 새로운 가용 리스트의 헤드가 됨
        free_listp = SUCC_FREEP(bp);
    }
    // 그렇지 않은 경우 (중간이나 마지막 블록을 제거할 때)
    else{
        // bp 이전 블록의 다음 블록 포인터를 bp의 다음 블록 포인터로 설정하여 연결을 유지
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        // bp 다음 블록의 이전 블록 포인터를 bp의 이전 블록 포인터로 설정하여 연결을 유지
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
}
