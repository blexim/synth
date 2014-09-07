#ifndef HEAPTHEORY_H
#define HEAPTHEORY_H

#include "synth.h"

#ifndef NSTACK
 #define NSTACK 0
#endif

#ifndef NHEAP
 #define NHEAP 3
#endif

int path_length(word_t args[NARGS], word_t x, word_t y);
int path(word_t args[NARGS], word_t x, word_t y);
int onpath(word_t args[NARGS], word_t x, word_t y, word_t z);
int alias(word_t args[NARGS], word_t x, word_t y);
int update(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y);
int assign(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y);
int lookup(word_t pre[NARGS], word_t post[NARGS], word_t x, word_t y);

#endif
