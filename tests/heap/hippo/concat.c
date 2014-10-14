#include "heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmp = 3;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;

  return !alias(pre, x, null_ptr) &&
         alias(pre, x, tmp);
}

int cond(abstract_heapt *heap) {
  abstract_heapt h;

  abstract_lookup(heap, &h, tmp, tmp);

  return !alias(&h, tmp, null_ptr);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (alias(pre, tmp, null_ptr)) {
    return 0;
  }

  abstract_lookup(pre, post, tmp, tmp);
  return 1;
}

int assertion(abstract_heapt *heap) {
  abstract_heapt h;

  abstract_update(heap, &h, tmp, y);

  return is_path(&h, x, tmp);
}

int inv(abstract_heapt *heap) {
  return !alias(heap, tmp, null_ptr) && is_path(heap, x, tmp);
}
