#include "heap.h"

ptr_t x = 1;
ptr_t p = 2;

int pre(abstract_heapt *heap) {
  return alias(heap, p, x);
}

int cond(abstract_heapt *heap) {
  return !alias(heap, p, null_ptr);
}

int inv(abstract_heapt *heap) {
  return is_path(heap, x, p);
}

int body(abstract_heapt *pre, abstract_heapt *post) {
  if (alias(pre, p, null_ptr)) {
    return 0;
  }

  abstract_lookup(pre, post, p, p);

  return 1;
}

int assertion(abstract_heapt *heap) {
  return is_path(heap, x, null_ptr);
}

void main(void) {
  abstract_heapt h, t;

  if (!valid_abstract_heap(&h)) {
    return;
  }

  // Base.
  if (pre(&h)) {
    assert(inv(&h));
  }

  // Induction.
  if (inv(&h) && cond(&h)) {
    assert(body(&h, &t));
    assert(inv(&t));
  }

  // Property.
  if (inv(&h) && !cond(&h)) {
    assert(assertion(&h));
  }
}
