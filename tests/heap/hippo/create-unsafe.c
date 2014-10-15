#include "heap.h"
#include "state.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t aux = 3;

int pre(statet *pre_state, statet *post_state) {
  abstract_heapt *pre = &(pre_state->heap);
  abstract_heapt *post = &(post_state->heap);
  abstract_heapt t1;

  *post_state = *pre_state;

  abstract_new(pre, &t1, x);

  if (is_null(&t1, x)) {
    return 0;
  }

  abstract_assign(&t1, post, y, x);

  return 1;
}

int cond(statet *state) {
  word_t len = state->stack[0];
  abstract_heapt *heap = &(state->heap);

  return path_len(heap, x, y) < len;
}

int body(statet *pre_state, statet *post_state) {
  abstract_heapt *pre = &(pre_state->heap);
  abstract_heapt *post = &(post_state->heap);
  abstract_heapt t1, t2;

  *post_state = *pre_state;

  abstract_new(pre, &t1, aux);

  if (is_null(&t1, y)) {
    return 0;
  }

  abstract_update(&t1, &t2, y, aux);
  abstract_assign(&t2, post, y, aux);

  return 1;
}

int assertion(statet *state) {
  abstract_heapt *heap = &(state->heap);
  abstract_heapt t1;

  if (is_null(heap, y)) {
    return 0;
  }

  abstract_update(heap, &t1, y, x);

  return is_path(&t1, x, null_ptr);
}

word_t rank1(statet *state) {
  abstract_heapt *heap = &(state->heap);
  word_t len = state->stack[0];

  return len - path_len(heap, x, y);
}

word_t rank2(statet *heap) {
  return 1;
}

int init(statet *heap) {
  return 1;
}

int danger(statet *state) {
  abstract_heapt *heap = &(state->heap);

  return !is_null(heap, x) &&
         is_path(heap, x, y);
}
