#include "heap.h"

ptr_t x = 1;
ptr_t tmp = 2;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;
  return alias(post, x, tmp);
}

int cond(abstract_heapt *heap) {
  return !is_null(heap, tmp) && nondet();
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (is_null(pre, tmp)) {
    return 0;
  }

  abstract_lookup(pre, post, tmp, tmp);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, x, tmp);
}

int inv(abstract_heapt *heap) {
  return is_path(heap, x, tmp);
}
