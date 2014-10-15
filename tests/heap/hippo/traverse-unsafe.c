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

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (is_null(pre, p)) {
    return 0;
  }

  abstract_heapt t1;

  abstract_lookup(pre, &t1, p, p);

  if (is_null(&t1, p)) {
    return 0;
  }

  abstract_lookup(&t1, post, p, p);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, x, null_ptr);
}

word_t rank1(abstract_heapt *heap) {
  return 1;
}

word_t rank2(abstract_heapt *heap) {
  return 1;
}

int init(abstract_heapt *heap) {
  return path_len(heap, p, null_ptr) == 1;
}

int danger(abstract_heapt *heap) {
  return path_len(heap, p, null_ptr) == 1;
}
