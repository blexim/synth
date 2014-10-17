#include "heap.h"
#include "state.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t aux = 3;

int pre(statet *pre, statet *post) {
  abstract_heapt t1;
  *post = *pre;

  abstract_new(&(pre->heap), &t1, x);

  if (is_null(&t1, x)) {
    return 0;
  }

  abstract_assign(&t1, &(post->heap), y, x);

  return 1;
}

int cond(statet *state) {
  abstract_heapt *heap = &(state->heap);
  word_t len = state->stack[0];

  return len < path_len(heap, x, null_ptr);
}

int body(statet *pre, statet *post) {
  abstract_heapt t1, t2;
  *post = *pre;

  abstract_new(&(pre->heap), &t1, aux);

  if (is_null(&t1, y)) {
    return 0;
  }

  abstract_update(&t1, &t2, y, aux);
  abstract_assign(&t2, &(post->heap), y, aux);

  return 1;
}

int assertion(statet *state) {
  abstract_heapt *heap = &(state->heap);
  abstract_heapt t1;

  if (is_null(heap, y)) {
    return 0;
  }

  abstract_update(heap, &t1, y, null_ptr);

  return is_path(&t1, x, null_ptr);
}

int inv(statet *state) {
  abstract_heapt *heap = &(state->heap);

  return !is_null(heap, y) &&
         is_path(heap, x, y);
}
