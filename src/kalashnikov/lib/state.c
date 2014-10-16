#include "synth.h"
#include "heap.h"
#include "state.h"

#define heap(s) &((s)->heap)

int valid_state(statet *state) {
  return valid_abstract_heap(heap(state));
}

void deserialize_state(word_t args[NARGS], statet *state) {
  word_t i, j;

  j = 0;
  for (i = 0; i < NSTACK; i++) {
    state->stack[i] = args[j++];
  }

#ifdef HEAP
  abstract_heapt *heap = heap(state);

  for (i = 0; i < NABSNODES; i++) {
    heap->succ[i] = args[j++];
    heap->dist[i] = args[j++];
  }

  for (i = 0; i < NHEAP; i++) {
    heap->ptr[i] = args[j++];
  }

  heap->nnodes = args[j++];
#endif
}

void serialize_state(statet *state, word_t args[NARGS]) {
  word_t i, j;

  j = 0;
  for (i = 0; i < NSTACK; i++) {
    args[j++] = state->stack[i];
  }

#ifdef HEAP
  abstract_heapt *heap = heap(state);

  for (i = 0; i < NABSNODES; i++) {
    args[j++] = heap->succ[i];
    args[j++] = heap->dist[i];
  }

  for (i = 0; i < NHEAP; i++) {
    args[j++] = heap->ptr[i];
  }

  args[j++] = heap->nnodes;
#endif
}

void heap_new(statet *pre, statet *post, ptr_t x) {
  *post = *pre;

  abstract_new(heap(pre), heap(post), x);
}

void heap_assign(statet *pre, statet *post, ptr_t x, ptr_t y) {
  *post = *pre;

  abstract_assign(heap(pre), heap(post), x, y);
}

void heap_lookup(statet *pre, statet *post, ptr_t x, ptr_t y) {
  *post = *pre;

  abstract_lookup(heap(pre), heap(post), x, y);
}

void heap_update(statet *pre, statet *post, ptr_t x, ptr_t y) {
  *post = *pre;

  abstract_update(heap(pre), heap(post), x, y);
}
