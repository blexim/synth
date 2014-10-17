#ifndef STATE_H
#define STATE_H

#include "synth.h"
#include "heap.h"

#ifndef NSTACK
 #define NSTACK 0
#endif

typedef struct state {
  abstract_heapt heap;
  word_t stack[NSTACK];
} statet;

void alloc(statet *pre, statet *post, ptr_t x);
void assign(statet *pre, statet *post, ptr_t x, ptr_t y);
void lookup(statet *pre, statet *post, ptr_t x, ptr_t y);
void update(statet *pre, statet *post, ptr_t x, ptr_t y);


#endif // STATE_H
