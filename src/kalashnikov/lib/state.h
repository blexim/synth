#ifndef STATE_H
#define STATE_H

#include "synth.h"
#include "heap.h"

#ifndef NSTACK
 #define NSTACK NARGS
#endif

typedef struct state {
#ifdef HEAP
  abstract_heapt heap;
#endif

  word_t stack[NSTACK];
} statet;

int valid_state(statet *state);

void deserialize_state(word_t args[NARGS], statet *state);
void serialize_state(statet *state, word_t args[NARGS]);

void heap_new(statet *pre, statet *post, ptr_t x);
void heap_assign(statet *pre, statet *post, ptr_t x, ptr_t y);
void heap_lookup(statet *pre, statet *post, ptr_t x, ptr_t y);
void heap_update(statet *pre, statet *post, ptr_t x, ptr_t y);


#endif // STATE_H
