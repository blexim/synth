#include "heap.h"

extern int pre(abstract_heapt *heap, abstract_heapt *post);
extern int cond(abstract_heapt *heap);
extern int body(abstract_heapt *pre, abstract_heapt *post);
extern int assertion(abstract_heapt *heap);
extern int inv(abstract_heapt *heap);

void main(void) {
  abstract_heapt h, t1, t2;

  assert(NABSNODES >= (NLIVE*2) + 1);

  if (!valid_abstract_heap(&h)) {
    return;
  }

  // Base.
  if (pre(&h, &t1)) {
    assert(inv(&t1));
  }

  if (inv(&h)) {
    if (cond(&h)) {
      // Induction.
      assert(body(&h, &t2));
      assert(inv(&t2));
    } else {
      // Property.
      assert(assertion(&h));
    }
  }
}
