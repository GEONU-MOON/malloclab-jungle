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
    "Week05_team9",
    /* First member's full name */
    "Geonu Moon",
    /* First member's email address */
    "moondy220965@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Junseong Choi",
    /* Second member's email address (leave blank if none) */
    "choigo@naver.com"
};

#define WSIZE 4      // 워드 크기
#define DSIZE 8      // 이중 워드 크기
#define CHUNKSIZE (1<<12) // 확장할 힙의 기본 크기

#define MAX(x,y) ((x) > (y) ? (x) : (y)) // 두 값 중 큰 값을 반환하는 매크로

#define PACK(size, alloc) ((size) | (alloc)) // 사이즈와 할당 비트를 합친 값을 반환하는 매크로

#define GET(p) (*(unsigned int*)(p)) // 포인터 p가 가리키는 값을 읽는 매크로
#define PUT(p, val) (*(unsigned int*)(p) = (val)) // 포인터 p가 가리키는 위치에 값을 쓰는 매크로

#define GET_SIZE(p) (GET(p) & ~0x7) // 블록 헤더의 크기를 반환하는 매크로
#define GET_ALLOC(p) (GET(p) & 0x1) // 블록 헤더의 할당 여부를 반환하는 매크로

#define HDRP(bp) ((char*)(bp) - WSIZE) // bp가 어디에있던 상관없이 WSIZE 앞에 위치한다.
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감.)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)

static char *heap_listp; // 힙 리스트의 시작 포인터
static char *last_bp; // 마지막으로 할당된 블록을 추적하기 위한 포인터
static void *extend_heap(size_t words); // 힙을 확장하는 함수
static void *next_fit(size_t asize); // 적절한 블록을 찾는 함수
static void place(void *bp, size_t asize); // 블록을 할당하는 함수
static void *coalesce(void *bp); // 블록을 병합하는 함수

/*
mem_sbrk(intptr_t increment): 운영체제에게 추가적인 메모리 공간을 요청합니다. increment는 요청하는 바이트 수입니다.
heap_listp: 힙 리스트의 시작을 가리키는 전역 변수입니다.
WSIZE: 워드 사이즈(바이트)를 나타내는 상수.
DSIZE: 더블 워드 사이즈(바이트)를 나타내는 상수.
CHUNKSIZE: 추가 메모리를 요청할 때 사용되는 기본적인 크기 상수입니다.

mem_sbrk(4 * WSIZE)를 사용하여 초기 프롤로그 블록을 추가합니다. 이를 위해 운영체제에게 4워드 크기(4 * WSIZE)의 메모리 공간을 요청합니다. 만약 힙 초기화에 실패하면 -1을 반환합니다.
프롤로그 블록을 초기화합니다:
첫 번째 워드는 패딩을 추가하여 정렬을 맞춥니다.
두 번째 워드는 프롤로그 헤더로 설정되어 크기 DSIZE의 할당된 블록을 나타냅니다.
세 번째 워드는 프롤로그 풋터로 설정되어 크기 DSIZE의 할당된 블록을 나타냅니다.
네 번째 워드는 에필로그 헤더로 설정되어 힙의 끝을 나타내며 할당되지 않은 상태를 나타냅니다.
heap_listp를 프롤로그 블록 다음 위치로 설정합니다.
extend_heap(CHUNKSIZE / WSIZE)를 사용하여 힙을 초기화하고 초기 프롤로그 블록을 추가합니다. 이를 위해 운영체제에게 추가적인 메모리 공간을 요청합니다. 만약 힙 초기화에 실패하면 -1을 반환합니다.
last_bp를 초기화된 힙 리스트의 시작으로 설정합니다.
초기화가 성공하면 0을 반환합니다.
*/
int mm_init(void) {
    // 힙을 초기화하기 위해 초기 프롤로그 블록을 추가
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1; // 힙 초기화 실패 시 -1 반환
    }
    PUT(heap_listp, 0); // Alignment Padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // Epilogue Header
    heap_listp += (2 * WSIZE); // 힙 리스트 포인터를 설정하여 프롤로그 블록 다음 위치로 이동

    // 힙을 초기화하는 동안 프롤로그 블록 추가
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1; // 힙 확장 실패 시 -1 반환
    }
    last_bp = (char *)heap_listp; // 초기화된 힙 리스트의 시작을 last_bp에 저장

    return 0; // 성공 시 0 반환
}

// 힙을 확장하는 함수
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

/*
size_t size: 요청된 메모리 블록의 크기.
size_t asize: 실제 할당될 메모리 블록의 크기.
size_t extendsize: 필요한 경우 힙을 확장할 크기.
char *bp: 메모리 블록을 가리키는 포인터.

size가 0이면 NULL을 반환합니다.
size가 DSIZE보다 작거나 같으면, 할당되는 블록의 최소 크기인 2 * DSIZE로 설정합니다.
그렇지 않으면, 요청된 크기에 맞게 블록을 정렬하고 추가적인 헤더 및 풋터 공간을 고려하여 할당되는 크기를 결정합니다.
next_fit 함수를 사용하여 적절한 가용 블록을 찾습니다.
만약 가용 블록을 찾으면, place 함수를 사용하여 메모리를 할당하고 초과 부분을 분할합니다. 그 후 last_bp를 업데이트하고 할당한 블록의 포인터를 반환합니다.
가용 블록을 찾지 못하면, 필요한 경우 힙을 확장하여 추가 메모리를 할당합니다.
확장할 크기는 요청된 크기와 CHUNKSIZE 중 더 큰 값을 선택합니다.
extend_heap 함수를 사용하여 힙을 확장하고, 성공하면 메모리를 할당하고 초과 부분을 분할합니다.
마지막으로 last_bp를 업데이트하고 할당한 블록의 포인터를 반환합니다.
*/
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = next_fit(asize)) != NULL) { // 가용블록 검색
        place(bp, asize); // 초과 부분 분할 새 할당한 블록 포인터 반환
        last_bp = bp;
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}

// 메모리 해제 함수
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// 블록 병합 함수
static void *coalesce(void *bp) {
    // 이전 블록과 다음 블록의 할당 여부 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 여부
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    // 이전 블록과 다음 블록이 모두 할당된 경우
    if (prev_alloc && next_alloc) {
        last_bp = bp; // 마지막 할당된 블록 업데이트
        return bp; // 병합할 필요 없이 현재 블록 반환
    } else if (prev_alloc && !next_alloc) { // 다음 블록만 비어 있는 경우
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록과 다음 블록의 크기 합침
        PUT(HDRP(bp), PACK(size, 0)); // 합친 크기로 헤더 업데이트
        PUT(FTRP(bp), PACK(size, 0)); // 합친 크기로 푸터 업데이트
    } else if (!prev_alloc && next_alloc) { // 이전 블록만 비어 있는 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 블록과 이전 블록의 크기 합침
        PUT(FTRP(bp), PACK(size, 0)); // 합친 크기로 푸터 업데이트
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 합친 크기로 이전 블록의 헤더 업데이트
        bp = PREV_BLKP(bp); // 이전 블록으로 이동
    } else { // 이전 블록과 다음 블록이 모두 비어 있는 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 세 개의 블록 크기 합침
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 합친 크기로 이전 블록의 헤더 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 합친 크기로 다음 블록의 푸터 업데이트
        bp = PREV_BLKP(bp); // 이전 블록으로 이동
    }
    last_bp = bp; // 마지막 할당된 블록 업데이트
    return bp; // 병합된 블록 포인터 반환
}

// 메모리 재할당 함수
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

// 적절한 블록을 찾는 함수
/*
size_t asize: 요청된 메모리 블록의 크기.
char *bp: 현재 포인터 위치를 나타내는 변수.
last_bp: 마지막 할당된 블록을 나타내는 전역 변수.

last_bp를 시작점으로 설정합니다. 이는 마지막으로 할당된 블록의 다음 블록을 가리키도록 함.
for 루프에서는 last_bp부터 힙의 끝까지 블록을 순회하며 다음을 검사.
해당 블록이 할당되지 않았고, 요청된 크기보다 크거나 같은 경우.
만약 조건이 충족되면 해당 블록을 반환하고, last_bp를 업데이트합니다.
while 루프에서는 힙의 시작부터 last_bp 직전까지 블록을 순회하며 위와 같은 조건을 검사.
적절한 블록을 찾지 못하면 NULL을 반환.
*/
static void *next_fit(size_t asize) {
    char *bp = last_bp; // 현재 포인터 위치부터 검색 시작

    // 마지막 할당된 블록부터 시작하여 끝까지 탐색
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        // 할당되지 않은 블록이고 요청된 크기보다 크거나 같은 경우
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp; // 마지막 할당된 블록을 업데이트
            return bp; // 해당 블록 반환
        }
    }

    // 힙 리스트의 처음부터 마지막 할당된 블록 이전까지 탐색
    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        // 할당되지 않은 블록이고 요청된 크기보다 크거나 같은 경우
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp; // 마지막 할당된 블록을 업데이트
            return bp; // 해당 블록 반환
        }
    }

    return NULL; // 적절한 블록을 찾지 못한 경우 NULL 반환
}

// 블록을 할당하는 함수
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 가져옴

    if ((csize - asize) >= (2 * DSIZE)) { // 남은 공간이 충분하면 분할
        PUT(HDRP(bp), PACK(asize, 1)); // 블록 헤더를 할당된 상태로 설정
        PUT(FTRP(bp), PACK(asize, 1)); // 블록 푸터를 할당된 상태로 설정
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 공간을 가진 블록의 헤더 설정
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 남은 공간을 가진 블록의 푸터 설정
    } else { // 남은 공간이 충분하지 않으면 블록을 분할하지 않고 모두 할당
        PUT(HDRP(bp), PACK(csize, 1)); // 블록 헤더를 할당된 상태로 설정
        PUT(FTRP(bp), PACK(csize, 1)); // 블록 푸터를 할당된 상태로 설정
    }
}