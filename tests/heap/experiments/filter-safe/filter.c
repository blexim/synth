#include "heap.h"

ptr_t x = 1;
ptr_t a = 2;
ptr_t b = 3;
ptr_t c = 4;

int pre(abstract_heapt *pre, abstract_heapt *post) {
  return 1;
}

int cond(abstract_heapt *heap) {
  return !is_null(heap, a);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  abstract_heapt t1, t2;

  if (alias(pre, a, x) && nondet()) {
    // We're dropping the head.
    if (is_null(pre, x)) {
      return 0;
    }

    abstract_lookup(pre, &t1, x, x);
    abstract_assign(&t1, post, a, x);
  } else {
    if (is_null(pre, a)) {
      return 0;
    }

    abstract_lookup(pre, &t1, b, a);

    if (!is_null(&t1, b) && nondet()) {
      // We're dropping b.
      if (is_null(&t1, b)) {
        return 0;
      }

      abstract_lookup(&t1, &t2, c, b);

      if (is_null(&t2, a)) {
        return 0;
      }

      abstract_update(&t2, post, a, c);
    } else {
      // Bump a.
      if (is_null(pre, a)) {
        return 0;
      }

      abstract_lookup(pre, post, a, a);
    }
  }

  return 1;
}

int assertion(abstract_heapt *heap) {
  return 1;
}

int inv(abstract_heapt *heap) {
  return 1;
}
