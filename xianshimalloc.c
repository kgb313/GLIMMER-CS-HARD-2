//头文件
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>


void *mm_sbrk(int incr);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit_first(size_t asize);
static void *find_fit_best(size_t asize);
static void delete_from_free_list(void *bp);
static void add_to_free_list(void *bp);
static void place(void *bp, size_t asize);


#define WSIZE       8   // 头部或指针字段的字节数（64 位一个字）
#define DSIZE       16  // 双字大小，块与负载的对齐粒度
#define CHUNKSIZE  (1 << 12)       // 扩展堆时的默认字节数
#define MAX_HEAP   (5 * (1 << 20)) // 模拟堆区上限（5MB）
#define MIN_BLK_SIZE (2 * DSIZE)   // 最小块大小（须容纳 hdr + pred + succ + ftr）

#define ALIGN(size) (((size) + (DSIZE - 1)) & ~(DSIZE - 1)) // 向上对齐到 DSIZE 的倍数

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  // 返回较大值


#define PACK(size, prev_alloc, alloc) \
    (((size) & ~0x7) | ((prev_alloc) << 1) | (alloc))  // 将 size、前块分配位、本块分配位合并为一个字
#define PACK_PREV_ALLOC(val, prev_alloc) (((val) & ~0x2) | ((prev_alloc) << 1))  // 只更新 header 中的 prev_alloc 位
#define PACK_ALLOC(val, alloc) (((val) & ~0x1) | (alloc))  // 只更新 header 中的 alloc 位

#define GET(p)        (*(unsigned long *)(p))  // 读地址 p 处的一个字
#define PUT(p, val)   (*(unsigned long *)(p) = (val))  // 向地址 p 处写一个字

#define GET_SIZE(p)       (GET(p) & ~0x7)           // 从 header/footer 取出块大小
#define GET_ALLOC(p)      (GET(p) & 0x1)            // 本块是否已分配
#define GET_PREV_ALLOC(p) ((GET(p) >> 1) & 0x1)     // 物理上前一块是否已分配（已分配块可无 footer）

#define HDRP(bp)  ((char *)(bp) - WSIZE)  // 块头部指针（bp 为有效荷载起始地址）
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 块尾部指针（主要用于空闲块）

#define GET_PRED(bp)  ((char *)GET(bp))  // 空闲块负载处：前驱空闲块指针
#define SET_PRED(bp, val)  (PUT(bp, (unsigned long)(val)))
#define GET_SUCC(bp)  ((char *)GET((char *)(bp) + WSIZE))  // 空闲块负载 +8：后继空闲块指针
#define SET_SUCC(bp, val)  (PUT((char *)(bp) + WSIZE, (unsigned long)(val)))

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  // 下一块的有效荷载指针
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // 前一块的有效荷载指针（经前块 footer）

static char *heap_listp;      // 序言块有效荷载地址，物理堆遍历起点
static char *free_listp;      // 显式空闲链表表头
static char *mem_start_brk;   // 向 OS 预留的堆区起始地址
static char *mem_brk;         // 当前堆顶（mm_sbrk 在此基础上递增）
static char *mem_max_addr;    // 堆区上界（mem_start_brk + MAX_HEAP）

#ifdef DEBUG
#define VERBOSE 1  // 在调试模式下启用调试信息输出
#else
#define VERBOSE 0  // 默认不输出调试信息
#endif



//同part1的调试模式
static void print_heap_blocks(int verbose, const char* func) {
    if (verbose) {
        char *curbp = (char *)heap_listp;
        printf("\n=========================== %s ===========================\n", func);

        while (GET_SIZE(HDRP(curbp)) > 0) {
            printf("Address: %p\n", curbp);
            printf("Size: %lu\n", GET_SIZE(HDRP(curbp)));
            printf("Allocated: %lu\n", GET_ALLOC(HDRP(curbp)));
            printf("\n");
            curbp = NEXT_BLKP(curbp);
        }

        printf("Address: %p\n", curbp); // Should point to the end of the heap
        printf("Size: 0\n");
        printf("Allocated: 1\n");
        printf("=========================== %s ===========================\n", func);
    }
}

/**
 * 
 * 
 *
 * @brief 初始化内存分配器。
 *
 * 实现上文堆的衍生方式中指定的初始化，初始化全局变量，分好堆1堆2
 */
int mm_init(void){
    mem_start_brk=(char*)malloc(MAX_HEAP);
    if (mem_start_brk==NULL)
        return -1;
    mem_brk=mem_start_brk;
    mem_max_addr=mem_start_brk+MAX_HEAP;

    if ((heap_listp = mm_sbrk(4*WSIZE))==(void*)-1)
        return -1;

    PUT(heap_listp,0);
    PUT(heap_listp+WSIZE,PACK(DSIZE,1,1));
    PUT(heap_listp+2*WSIZE,PACK(DSIZE,1,1));
    PUT(heap_listp+3*WSIZE,PACK(0,1,1));
    heap_listp+=2*WSIZE;

    free_listp=NULL;

    if(extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}
;

/**
 * @brief 增加程序的数据空间。
 *
 * @param incr 要增加的字节数。
 *
 * @return 扩展后的内存起始地址；如果扩展失败，则返回 (void *)-1。
 *
 * 实现上文堆的衍生方式中的功能
 */
void *mm_sbrk(int incr){
    char *old_brk=mem_brk;
    if (incr<0||(mem_brk+incr)>mem_max_addr) {
        return (void*)-1;
    }
    mem_brk+=incr;
    return (void*)old_brk;
};

/**
 * @brief 扩展堆空间。
 *
 * @param words 要扩展的字数。
 *
 * @return 返回新扩展区域的起始地址；如果扩展失败，则返回 NULL。
 *
 * extend_heap函数是对mem_sbrk的一层封装，接收的参数是要分配的字数
 * 在堆初始化以及malloc找不到合适内存块时使用
 * 它首先对请求大小进行地址对齐，然后调用mem_sbrk获取空间
 */
static void *extend_heap(size_t words){
    char *bp;
    size_t size=ALIGN(words*WSIZE);

    if((long)(bp=mm_sbrk(size))==-1)
        return NULL;

    size_t prev_alloc=GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp),PACK(size,prev_alloc,0));
    PUT(FTRP(bp),PACK(size,prev_alloc,0));

    char *epilogue=NEXT_BLKP(bp);
    PUT(HDRP(epilogue),PACK(0,0,1));

    return coalesce(bp);
}

/**
 * @brief 查找适合分配的空闲块（首次适应）。
 *
 * @param asize 请求的块大小（以字节为单位）。
 *
 * @return 返回找到的适合的空闲块的指针；如果没有找到合适的空闲块，则返回 NULL。
 *
 * 该函数在空闲链表中查找第一个合适的块，以满足请求的大小。
 */
static void *find_fit_first(size_t asize){
    char *bp=free_listp;
    while (bp!=NULL) {
        if(GET_SIZE(HDRP(bp))>=asize)
            return bp;
        bp=GET_SUCC(bp);
    }
    return NULL;
}

//类似find_fit_first
static void *find_fit_best(size_t asize){
    char*bp=free_listp;
    char *best=NULL;
    size_t best_size=(size_t)-1;
    while (bp!=NULL) {
        size_t s=GET_SIZE(HDRP(bp));
        if(s>=asize&&s<best_size) {
            best=bp;
            best_size=s;
        }
        bp=GET_SUCC(bp);
    }
    return best;}

/**
 * @brief 将指定的块放置到分配状态。
 *
 * @param bp 要分配的块的起始地址。
 * @param asize 请求的块大小（以字节为单位）。
 *
 * 该函数将指定的块标记为已分配，并更新块的大小信息。
 */
static void place(void* bp, size_t asize){
    size_t csize=GET_SIZE(HDRP(bp));
    size_t prev_alloc=GET_PREV_ALLOC(HDRP(bp));
    delete_from_free_list(bp);

    if (csize-asize>=MIN_BLK_SIZE) {
        PUT(HDRP(bp),PACK(asize,prev_alloc,1));

        char *new_free=NEXT_BLKP(bp);
        PUT(HDRP(new_free),PACK(csize-asize,1,0));
        PUT(FTRP(new_free),PACK(csize-asize,1,0));

        add_to_free_list(new_free);
    } else {
        PUT(HDRP(bp),PACK(csize,prev_alloc,1));

        char *next_bp=NEXT_BLKP(bp);
        PUT(HDRP(next_bp),PACK_PREV_ALLOC(GET(HDRP(next_bp)),1));
    }
}


/**
 * @brief 合并相邻的空闲块。
 *
 * @param bp 要合并的块的起始地址。
 *
 * @return 合并后的块的起始地址。
 *
 * 该函数合并当前块与其相邻的空闲块，以减少内存碎片并增加大块的可用内存。
 */
static void* coalesce(void* bp){
    size_t prev_alloc=GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size=GET_SIZE(HDRP(bp));

    if(prev_alloc&&next_alloc) {
    } else if(prev_alloc&&(!next_alloc)) {
        char *next=NEXT_BLKP(bp);
        delete_from_free_list(next);
        size += GET_SIZE(HDRP(next));

        PUT(HDRP(bp), PACK(size,1,0));
        PUT(FTRP(bp), PACK(size,1,0));
    } else if(!prev_alloc&&next_alloc) {
        char *prev=PREV_BLKP(bp);
        delete_from_free_list(prev);
        size_t a=GET_PREV_ALLOC(HDRP(prev));
        size+=GET_SIZE(HDRP(prev));
        bp=prev;
        PUT(HDRP(bp),PACK(size,a,0));
        PUT(FTRP(bp),PACK(size,a,0));
    } else {
        char*next=NEXT_BLKP(bp);
        char*prev=PREV_BLKP(bp);
        delete_from_free_list(next);
        delete_from_free_list(prev);
        size_t a=GET_PREV_ALLOC(HDRP(prev));
        size+=GET_SIZE(HDRP(prev))+GET_SIZE(HDRP(next));
        bp=prev;
        PUT(HDRP(bp),PACK(size,a,0));
        PUT(FTRP(bp),PACK(size,a,0));
    }

    add_to_free_list(bp);
    return bp;
};

/**
 * @brief 从空闲链表中移除指定的空闲块。
 *
 * @param bp 要移除的空闲块的起始地址。
 *
 * 该函数将指定的空闲块从空闲链表中移除，以便将其标记为已分配。
 */
static void delete_from_free_list(void *bp){
    char *pred=GET_PRED(bp);
    char *succ=GET_SUCC(bp);
    if (pred!=NULL)
        SET_SUCC(pred,succ);
    else
        free_listp=succ;
    if (succ!=NULL)
        SET_PRED(succ,pred);
}

/**
 * @brief 将指定的空闲块插入到空闲链表中。
 *
 * @param bp 要插入的空闲块的起始地址。
 *
 * 该函数用头插法将指定的空闲块插入到空闲链表中，以便将其标记为可用的空闲块。
 */
static void add_to_free_list(void *bp){
    SET_PRED(bp,NULL);
    SET_SUCC(bp,free_listp);
    if (free_listp!=NULL)
        SET_PRED(free_listp,bp);
    free_listp=bp;
}

/**
 * @brief 分配内存块。
 *
 * @param size 请求的内存块大小（以字节为单位）。该大小包括块头和块尾所需的空间。
 *
 * @return 返回分配的内存块的起始地址；如果分配失败，则返回 NULL。
 *
 * 该函数根据请求的大小在堆中查找适合的空闲块，如果找到合适的块则分配该块，并返回其起始地址。如果没有足够的空间，则可能会扩展堆或返回 NULL。
 */
void *mm_malloc(size_t size){
    if (size==0)
        return NULL;

    size_t asize=ALIGN(size+WSIZE);
    if (asize<MIN_BLK_SIZE)
        asize=MIN_BLK_SIZE;

    char *bp=find_fit_first(asize);
    if (bp!=NULL) {
        place(bp,asize);
        return bp;
    }

    size_t extendsize=MAX(asize,CHUNKSIZE);
    if ((bp=extend_heap(extendsize/WSIZE))==NULL)
        return NULL;

    place(bp,asize);
    print_heap_blocks(1,"malloc");
    return bp;
};

/**
 * @brief 释放内存块。
 *
 * @param bp 要释放的内存块的起始地址。
 *
 * 该函数将指定的内存块标记为已释放，并尝试将其合并到相邻的空闲块中，以减少内存碎片。
 */
void mm_free(void *bp){
    if (bp==NULL)
        return;

    size_t size=GET_SIZE(HDRP(bp));
    size_t prev_alloc=GET_PREV_ALLOC(HDRP(bp));

    PUT(HDRP(bp),PACK(size,prev_alloc,0));
    PUT(FTRP(bp),PACK(size,prev_alloc,0));

    char *next_bp=NEXT_BLKP(bp);
    PUT(HDRP(next_bp),PACK_PREV_ALLOC(GET(HDRP(next_bp)),0));

    coalesce(bp);
    print_heap_blocks(1,"free");
};

/**
 * @brief 重新分配内存块。
 *
 * @param ptr 指向要重新分配的内存块的起始地址。如果 ptr 为 NULL，则相当于调用 mm_malloc。
 * @param size 请求的新内存块大小（以字节为单位）。该大小包括块头和块尾所需的空间。
 *
 * @return 返回重新分配的内存块的起始地址；如果重新分配失败，则返回 NULL。
 *
 * 该函数调整指定内存块的大小。如果新的大小大于原始大小，会在堆中分配新的内存块，并将原始数据复制到新内存块中。如果新的大小小于原始大小，则会截断原始数据。原始内存块的内容在重新分配之前被保留。
 */
void *mm_realloc(void *ptr, size_t size){
    if (ptr==NULL)
        return mm_malloc(size);
    if (size==0) {
        mm_free(ptr);
        return NULL;
    }
    size_t oldsize=GET_SIZE(HDRP(ptr));
    size_t asize=ALIGN(size + WSIZE);
    if (asize<MIN_BLK_SIZE)
        asize=MIN_BLK_SIZE;
    if (asize==oldsize)
        return ptr;
    if (asize<oldsize) {
        if (oldsize-asize>=MIN_BLK_SIZE) {
            size_t prev_alloc=GET_PREV_ALLOC(HDRP(ptr));
            PUT(HDRP(ptr),PACK(asize,prev_alloc,1));

            char *new_free=NEXT_BLKP(ptr);
            PUT(HDRP(new_free),PACK(oldsize-asize,1,0));
            PUT(FTRP(new_free),PACK(oldsize-asize,1,0));

            char *after=NEXT_BLKP(new_free);
            PUT(HDRP(after),PACK_PREV_ALLOC(GET(HDRP(after)),0));

            coalesce(new_free);
        }
        return ptr;
    }
    char *next_bp=NEXT_BLKP(ptr);
    if (GET_ALLOC(HDRP(next_bp))==0) {
        size_t next_size=GET_SIZE(HDRP(next_bp));
        size_t total=oldsize+next_size;
        if (total>=asize) {
            size_t prev_alloc=GET_PREV_ALLOC(HDRP(ptr));
            delete_from_free_list(next_bp);

            if (total-asize>=MIN_BLK_SIZE) {
                PUT(HDRP(ptr),PACK(asize,prev_alloc,1));

                char *new_free=NEXT_BLKP(ptr);
                PUT(HDRP(new_free),PACK(total-asize,1,0));
                PUT(FTRP(new_free),PACK(total-asize,1,0));

                char *after=NEXT_BLKP(new_free);
                PUT(HDRP(after),PACK_PREV_ALLOC(GET(HDRP(after)),0));

                add_to_free_list(new_free);
            } else {
                PUT(HDRP(ptr),PACK(total,prev_alloc,1));

                char *after=NEXT_BLKP(ptr);
                PUT(HDRP(after),PACK_PREV_ALLOC(GET(HDRP(after)),1));
            }
            return ptr;
        }
    }
    void *newptr = mm_malloc(size);
    if (newptr==NULL)
        return NULL;

    size_t copy_size=oldsize-WSIZE;
    if (size<copy_size)
        copy_size=size;
    memcpy(newptr,ptr,copy_size);
    mm_free(ptr);
    return newptr;
};

//测试用例
int main() {
    if (mm_init() == -1) {
        printf("Memory manager initialization failed.\n");
        return -1;
    }

    void *p1 = mm_malloc(8000);
    void *p2 = mm_malloc(200);
    void *p3 = mm_malloc(50);

    mm_free(p2);

    void *p4 = mm_malloc(150);

    mm_free(p1);
    mm_free(p3);
    mm_free(p4);

    return 0;
}