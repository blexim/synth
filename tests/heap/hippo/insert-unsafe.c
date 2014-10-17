#include "heap.h"

ptr_t x = 1;
ptr_t y = 2;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;
  return 1;
}

int cond(abstract_heapt *heap) {
  return 0;
}

int inv(abstract_heapt *heap) {
  return 1;
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  *post = *pre;
  return 1;
}

int assertion(abstract_heapt *heap) {
  abstract_heapt t1, t2;

  abstract_new(heap, &t1, x);

  if (is_null(&t1, x)) {
    return 0;
  }

  t2 = t1;

  if (!is_path(&t2, x, y)) {
    return 0;
  }

  return 1;
}
word_t rank1(abstract_heapt *heap) {
  return 1;
}

word_t rank2(abstract_heapt *heap) {
  return 1;
}

int init(abstract_heapt *heap) {
  return !is_null(heap, y);
}

int danger(abstract_heapt *heap) {
  return !is_null(heap, y);
}
