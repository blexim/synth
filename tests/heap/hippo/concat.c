#include "heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmp = 3;

int pre(abstract_heapt *heap) {
  return !alias(heap, x, null_ptr) &&
         alias(heap, x, tmp);
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
}

int assertion(abstract_heapt *heap) {
  abstract_heapt h;

  abstract_update(heap, &h, tmp, y);

  return is_path(&h, x, tmp);
}



