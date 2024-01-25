//
// Created by os on 12/11/23.
//


#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "fs.h"

extern char end[];
extern struct proc proc[NPROC];

//swap disc = 16MB = 2^24B
//block size on disc = 1KB = 2^10B
//blocks on swap disc = 2^24/2^10 = 2^14
//bit vector for free blocks on swap disc = 2^14 / 2^6 = 2^8
//if bit is 0 block is free
struct {
    uint64 bitVector[256];
    struct spinlock lock;
} swapDisc;

//ram = 16MB = 2^24B
//page = 4KB = 2^12B
//ram/page = 2^12 = 4096
#define MAXPAGES 4096   // maximum pages in ram

struct referenceHistoryBits {
    pagetable_t pagetable;
    uint64 va;
    uint64 refHistBits;
    uint8 used;
};

struct {
    struct referenceHistoryBits referenceHistoryBits[MAXPAGES];
    struct spinlock lock;
} pageList;

void psinit() {
    initlock(&swapDisc.lock, "swapdisc");
    memset(swapDisc.bitVector, 0, sizeof(swapDisc.bitVector));
    initlock(&pageList.lock, "pagelist");
    memset(pageList.referenceHistoryBits, 0, sizeof(pageList.referenceHistoryBits));
}

void addPageToList(pagetable_t pagetable, uint64 va) {
    acquire(&pageList.lock);
    for(int i = 0; i < MAXPAGES; i++) {
        if(!pageList.referenceHistoryBits[i].used) {
            pageList.referenceHistoryBits[i].used = 1;
            pageList.referenceHistoryBits[i].pagetable = pagetable;
            pageList.referenceHistoryBits[i].va = va;
            pageList.referenceHistoryBits[i].refHistBits = 0;
            break;
        }
    }
    release(&pageList.lock);
}

void removePageFromList(pagetable_t pagetable, uint64 va) {
    acquire(&pageList.lock);
    for(int i = 0; i < MAXPAGES; i++) {
        if(pageList.referenceHistoryBits[i].pagetable == pagetable && pageList.referenceHistoryBits[i].va == va && pageList.referenceHistoryBits[i].used == 1) {
            pageList.referenceHistoryBits[i].used = 0;
            break;
        }
    }
    release(&pageList.lock);
}

void updateReferenceBits() {
    acquire(&pageList.lock);
    for(int i = 0; i < MAXPAGES; i++) {
        if(pageList.referenceHistoryBits[i].used) {
            pageList.referenceHistoryBits[i].refHistBits >>= 1;
            pte_t *pte = walk(pageList.referenceHistoryBits[i].pagetable, pageList.referenceHistoryBits[i].va, 0);
            uint8 update = 0;
            if (*pte & PTE_A) {
                update = 1;
                *pte |= PTE_WS;
            }
            pageList.referenceHistoryBits[i].refHistBits |= (uint64) update << 63;
            *pte &= ~PTE_A;
        }
    }
    release(&pageList.lock);
}

int cursor = 0;

uint64 getLRUPage(uint64 freeBlock) {
    uint64 first = 1, minRef = 0, minI = 0;
    acquire(&pageList.lock);
    for(int i = 0; i < MAXPAGES; i++) {
        if(pageList.referenceHistoryBits[cursor].used) {
            if(first || pageList.referenceHistoryBits[cursor].refHistBits < minRef) {
                first = 0;
                minI = cursor;
                minRef = pageList.referenceHistoryBits[cursor].refHistBits;
            }
        }
        cursor++;
        if(cursor == MAXPAGES) cursor = 0;
    }
    cursor = minI + 1;
    release(&pageList.lock);

    pte_t *minPte = walk(pageList.referenceHistoryBits[minI].pagetable, pageList.referenceHistoryBits[minI].va, 0);
    removePageFromList(pageList.referenceHistoryBits[minI].pagetable, pageList.referenceHistoryBits[minI].va);
    uint64 page = PTE2PA(*minPte);
    *minPte &= ~PTE_V;
    *minPte |= PTE_DS;
    *minPte &= 0x3FF;
    *minPte |= DB2PTE(freeBlock);
    return page;
}

void *pageSwap() {
    uint64 freeBlock = get4FreeBlocks();
    if(freeBlock == -1) return 0;
    uint64 paSwapPage = getLRUPage(freeBlock);

    int l[NPROC] = {0};
    int i = 0;
    for(struct proc *p = proc; p < &proc[NPROC]; p++) {
        if(p->lock.locked) {
            release(&p->lock);
            l[i] = 1;
        }
        i++;
    }
    for(int i = 0; i < 4; i++) {
        write_block(freeBlock, (uchar *) paSwapPage, 1);
        paSwapPage += BSIZE;
        freeBlock++;
    }
    i = 0;
    for(struct proc *p = proc; p < &proc[NPROC]; p++) {
        if(l[i]) {
            acquire(&p->lock);
            l[i] = 0;
        }
        i++;
    }

    kfree((void *) (paSwapPage - 4 * BSIZE));
    return kalloc();
}

void returnPage(pte_t *pte, void *freePage) {
    uint64 blockOnDisc = PTE2DB(*pte);
    free4Blocks(blockOnDisc);
    *pte |= PTE_V;
    *pte &= ~PTE_DS;
    *pte &= 0x3FF;
    *pte |= PA2PTE((uint64) freePage);

    int l[NPROC] = {0};
    int i = 0;
    for(struct proc *p = proc; p < &proc[NPROC]; p++) {
        if(p->lock.locked) {
            release(&p->lock);
            l[i] = 1;
        }
        i++;
    }
    for(int i = 0; i < 4; i++) {
        read_block(blockOnDisc, (uchar *) freePage, 1);
        freePage += BSIZE;
        blockOnDisc++;
    }
    i = 0;
    for(struct proc *p = proc; p < &proc[NPROC]; p++) {
        if(l[i]) {
            acquire(&p->lock);
            l[i] = 0;
        }
        i++;
    }

}

uint64 get4FreeBlocks() {
    uint64 block;
    int blocksTaken = 0;
    acquire(&swapDisc.lock);
    for(int i = 0; i < 256; i++) {
        if(swapDisc.bitVector[i] != ~0) {
            uint64 mask = (uint64) 1 << 63;
            block = i * 64;
            for(int j = 0; j < 64; j++) {
                if((swapDisc.bitVector[i] & mask) == 0) {
                    swapDisc.bitVector[i] |= mask;
                    blocksTaken++;
                    if(blocksTaken == 4) break;
                }
                block++;
                mask >>= 1;
            }
            break;
        }
    }
    release(&swapDisc.lock);
    if(blocksTaken == 4) return block - 3;
    else return -1;
}

void free4Blocks(uint64 block) {
    if(block >= 16384) return;
    uint64 byte = block / 64;
    uint64 mask = (uint64)1 << (63 - block % 64);
    acquire(&swapDisc.lock);
    for(int i = 0; i < 4; i++) {
        swapDisc.bitVector[byte] &= ~mask;
        mask >>= 1;
    }
    release(&swapDisc.lock);
}


void trashing() {
    uint64 maxPages = (PHYSTOP - (uint64)end) / PGSIZE;
    uint16 numOfPages = 0;
    struct proc *p;

    for(p = proc; p < &proc[NPROC]; p++) {
        if(!p->pagetable) continue;
        numOfPages++;
        for(int i = 0; i < 512; i++) {
            pte_t *pte1 = &p->pagetable[i];
            if(*pte1 & PTE_V) {
                pagetable_t pagetable2 = (pagetable_t)PTE2PA(*pte1);
                numOfPages++;
                for(int j = 0; j < 512; j++) {
                    pte_t *pte2 = &pagetable2[j];
                    if(*pte2 & PTE_V) {
                        pagetable_t pagetable3 = (pagetable_t)PTE2PA(*pte2);
                        numOfPages++;
                        for(int k = 0; k < 512; k++) {
                            pte_t *pte3 = &pagetable3[k];
                            if(*pte3 & PTE_WS) {
                                numOfPages++;
                                *pte3 &= ~PTE_WS;
                            }
                        }
                    }
                }
            }
        }
    }

    if(numOfPages > maxPages) {
        for(p = proc; p < &proc[NPROC]; p++) {
            acquire(&p->lock);
            if(p->state == RUNNABLE) {
                p->state = SUSPENDED;
                release(&p->lock);
                break;
            }
            release(&p->lock);
        }
    } else if(numOfPages < maxPages * 3 / 4) {
        for(p = proc; p < &proc[NPROC]; p++) {
            acquire(&p->lock);
            if(p->state == SUSPENDED) {
                p->state = RUNNABLE;
                release(&p->lock);
                break;
            }
            release(&p->lock);
        }
    }
}
