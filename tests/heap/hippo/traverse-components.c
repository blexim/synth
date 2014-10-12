#include "heap.h"

ptr_t x = 1;
ptr_t p = 2;

int pre(abstract_heapt *heap) {
  return alias(heap, p, x);
}

int cond(abstract_heapt *heap) {
  return !alias(heap, p, null_ptr);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (alias(pre, p, null_ptr)) {
    return 0;
  }

  abstract_lookup(pre, post, p, p);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return 1;
  return is_path(heap, x, null_ptr);
}
