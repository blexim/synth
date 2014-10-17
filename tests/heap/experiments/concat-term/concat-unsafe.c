#include "heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmp = 3;

int init(abstract_heapt *heap) {
  return is_path(heap, x, null_ptr);
}

word_t rank1(abstract_heapt *heap) {
  return path_len(heap, tmp, null_ptr);
}

word_t rank2(abstract_heapt *heap) {
  return 1;
}

int pre(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;

  return !is_null(pre, x) &&
         alias(pre, x, tmp);
}

int cond(abstract_heapt *heap) {
  return !is_null(heap, tmp);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (is_null(pre, tmp)) {
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

int danger(abstract_heapt *heap) {
  return is_path(heap, tmp, null_ptr);
}

int inv(abstract_heapt *heap) {
  return !is_null(heap, tmp) && is_path(heap, x, tmp);
}
