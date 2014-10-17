#include "heap.h"

ptr_t x = 1;
ptr_t p = 2;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;

  return alias(pre, p, x);
}

int cond(abstract_heapt *heap) {
  return !alias(heap, p, null_ptr);
}

int inv(abstract_heapt *heap) {
  return is_path(heap, x, p);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (is_null(pre, p)) {
    return 0;
  }

  abstract_lookup(pre, post, p, p);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, x, null_ptr);
}
