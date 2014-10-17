#ifndef STATE_H
#define STATE_H

#include "synth.h"
#include "heap.h"

#ifndef NSTACK
 #define NSTACK 0
#endif

typedef struct state {
  word_t stack[NSTACK];
  abstract_heapt heap;
} statet;

void alloc(statet *pre, statet *post, ptr_t x);
void assign(statet *pre, statet *post, ptr_t x, ptr_t y);
void lookup(statet *pre, statet *post, ptr_t x, ptr_t y);
void update(statet *pre, statet *post, ptr_t x, ptr_t y);


#endif // STATE_H
