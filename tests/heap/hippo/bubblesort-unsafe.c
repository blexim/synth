#include "heap.h"

ptr_t p = 1;
ptr_t x = 2;
ptr_t tmp = 3;

int pre1(abstract_heapt *pre, abstract_heapt *post) {
  abstract_assign(pre, post, p, x);
}

int cond1(abstract_heapt *pre) {
  return nondet();
}

int pre2(abstract_heapt *pre, abstract_heapt *post) {
  abstract_assign(pre, post, p, x);
}

int cond2(abstract_heapt *pre) {
  return !is_null(pre, p);
}

int body2(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt t1;

  if (is_null(pre, p)) {
    return 0;
  }

  abstract_lookup(pre, &t1, tmp, p);

  if (is_null(&t1, p) ||
      is_null(&t1, tmp)) {
    return 0;
  }

  if (nondet()) {
    if (is_null(&t1, p)) {
      return 0;
    }
  }

  abstract_assign(&t1, post, p, tmp);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, x, p);
}

int inv1(abstract_heapt *heap) {
  return is_path(heap, x, p);
}

int inv2(abstract_heapt *heap) {
  return is_path(heap, x, p);
}
word_t rank1(abstract_heapt *heap) {
  return 1;
}

word_t rank2(abstract_heapt *heap) {
  return 1;
}

int init(abstract_heapt *heap) {
  return 1;
}

int danger(abstract_heapt *heap) {
  return 1;
}
