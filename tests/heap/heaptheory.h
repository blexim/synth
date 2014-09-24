#ifndef HEAPTHEORY_H
#define HEAPTHEORY_H

#include "synth.h"

#ifndef NHEAP
 #define NHEAP 0
#endif

#ifndef NSTACK
 #define NSTACK (NARGS - NHEAP*NHEAP)
#endif

#define idx(x, y) (NSTACK + (x * NHEAP) + y)

#define INF WORDMASK

unsigned int path_length(word_t args[NARGS], word_t x, word_t y);
unsigned int cycle_length(word_t args[NARGS], word_t x);
int path(word_t args[NARGS], word_t x, word_t y);
int onpath(word_t args[NARGS], word_t x, word_t y, word_t z);
int alias(word_t args[NARGS], word_t x, word_t y);
int update(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y);
int assign(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y);
int lookup(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y);
void alloc(word_t pre[NARGS], word_t post[NARGS], word_t x);
int well_formed(word_t vars[NARGS]);

#endif
