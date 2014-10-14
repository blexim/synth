#include "heap.h"

extern int pre(abstract_heapt *heap);
extern int cond(abstract_heapt *heap);
extern int body(abstract_heapt *pre, abstract_heapt *post);
extern int assertion(abstract_heapt *heap);
extern int inv(abstract_heapt *heap);

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
