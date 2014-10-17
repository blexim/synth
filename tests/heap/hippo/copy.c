#include "heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmpx = 3;
ptr_t tmpy = 4;
ptr_t cell = 5;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  if (is_null(pre, x)) {
    return 0;
  }

  if (!is_null(pre, y) ||
      !is_null(pre, tmpx) ||
      !is_null(pre, tmpy) ||
      !is_null(pre, cell)) {
    return 0;
  }

  abstract_heapt t1, t2;

  abstract_new(pre, &t1, y);
  abstract_lookup(&t1, &t2, tmpx, x);
  abstract_assign(&t2, post, tmpy, y);

  return 1;
}

int cond(abstract_heapt *heap) {
  return !is_null(heap, tmpx);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt t1, t2;

  *post = *pre;

  if (!is_null(pre, x) ||
      !is_null(pre, cell)) {
    return 1;
  }

  abstract_new(pre, &t1, cell);

  if (is_null(&t1, cell) ||
      is_null(&t1, tmpx) ||
      is_null(&t1, tmpy)) {
    return 0;
  }

  abstract_update(&t1, &t2, tmpy, cell);

  if (is_null(&t2, tmpx)) {
    return 0;
  }

  abstract_lookup(&t2, post, tmpx, tmpx);

  return 1;
}

int assertion(abstract_heapt *heap) {
  if (alias(heap, tmpy, null_ptr)) {
    return 0;
  }

  if (!is_path(heap, y, null_ptr)) {
    return 0;
  }

  return 1;
}

int inv(abstract_heapt *heap) {
  return !is_null(heap, tmpy) &&
         is_path(heap, y, null_ptr);
}
