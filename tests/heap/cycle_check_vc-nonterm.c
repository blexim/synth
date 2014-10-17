#include "heap.h"

ptr_t l = 1;
ptr_t p = 2;
ptr_t q = 3;


int cond(abstract_heapt *heap) {
  return !alias(heap, p, q) &&
         !is_null(heap, p) &&
         !is_null(heap, q);
}

#define cond_lookup(a, b, x) do { \
  if (!is_null(a, x)) { \
    if (is_null(a, x)) return 0; \
    abstract_lookup(a, b, x, x); \
  } else { \
    *(b) = *(a); \
  } \
}while (0)


int body(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt t1, t2, t3, t4, t5;

  cond_lookup(pre, &t1, p);
  cond_lookup(&t1, &t2, p);

  cond_lookup(&t2, &t3, q);
  cond_lookup(&t3, &t4, q);
  cond_lookup(&t4, &t5, q);
  cond_lookup(&t5, post, q);

  return 1;
}

int pre(abstract_heapt *pre, abstract_heapt *post) {
  if (alias(pre, p, l) && alias(pre, q, l) && !is_null(pre, l)) {
    abstract_lookup(pre, post, q, l);

    if (is_path(post, l, null_ptr) || is_path(post, q, l)) {
      return 1;
    } else {
      return 0;
    }
  } else {
    *post = *pre;
    return 0;
  }
}

int assertion(abstract_heapt *heap) {
  if (alias(heap, p, q)) {
    return !is_path(heap, l, null_ptr);
  } else {
    return is_path(heap, l, null_ptr);
  }
}

int inv(abstract_heapt *heap) {
  return is_path(heap, l, p) && is_path(heap, p, q) &&
         (is_path(heap, q, p) != is_path(heap, l, null_ptr));
}

word_t rank1(abstract_heapt *heap) {
  return path_len(heap, q, null_ptr);
}

word_t rank2(abstract_heapt *heap) {
  return path_len(heap, q, p);
}
