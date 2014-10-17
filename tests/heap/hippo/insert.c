#include "heap.h"
#include "state.h"

ptr_t x = 1;
ptr_t y = 2;

int pre(statet *pre, statet *post) {
  *post = *pre;
  return 1;
}

int cond(statet *heap) {
  return 0;
}

int inv(statet *heap) {
  return 1;
}

int body(statet *pre, statet *post) {
  *post = *pre;
  return 1;
}

int assertion(statet *state) {
  abstract_heapt t1, t2;

  abstract_new(&(state->heap), &t1, x);

  if (is_null(&t1, x)) {
    return 0;
  }

  abstract_update(&t1, &t2, x, y);

  if (!is_path(&t2, x, y)) {
    return 0;
  }

  return 1;
}
