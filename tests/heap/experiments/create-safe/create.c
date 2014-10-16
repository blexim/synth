#include "heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t aux = 3;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt t1;

  abstract_new(pre, &t1, x);

  if (is_null(&t1, x)) {
    return 0;
  }

  abstract_assign(&t1, post, y, x);

  return 1;
}

int cond(abstract_heapt *heap) {
  return nondet();
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt t1, t2;

  abstract_new(pre, &t1, aux);

  if (is_null(&t1, y)) {
    return 0;
  }

  abstract_update(&t1, &t2, y, aux);
  abstract_assign(&t2, post, y, aux);

  return 1;
}

int assertion(abstract_heapt *heap) {
  abstract_heapt t1;

  if (is_null(heap, y)) {
    return 0;
  }

  abstract_update(heap, &t1, y, null_ptr);

  return is_path(&t1, x, null_ptr);
}

int inv(abstract_heapt *heap) {
  return !is_null(heap, y) &&
         is_path(heap, x, y);
}
