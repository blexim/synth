#include "heap.h"

extern int pre1(abstract_heapt *heap, abstract_heapt *post);
extern int pre2(abstract_heapt *heap, abstract_heapt *post);

extern int cond1(abstract_heapt *heap);
extern int cond2(abstract_heapt *heap);

extern int body2(abstract_heapt *pre, abstract_heapt *post);

extern int assertion(abstract_heapt *heap);

extern int inv1(abstract_heapt *heap);
extern int inv2(abstract_heapt *heap);

void main(void) {
  abstract_heapt h, t1, t2, t3;

  //assert(NABSNODES >= (NLIVE*2) + 1);

  if (!valid_abstract_heap(&h)) {
    return;
  }

  // Base.
  if (pre1(&h, &t1)) {
    assert(inv1(&t1));
  }

  if (inv1(&h)) {
    if (cond1(&h)) {
      if (pre2(&h, &t2)) {
        // Establish inner invariant.
        assert(inv2(&t2));
      }
    } else {
      // Cond doesn't hold -- check the property.
      assert(assertion(&h));
    }
  }

  if (inv2(&h)) {
    if (cond2(&h)) {
      // Induction.
      assert(body2(&h, &t3));
      assert(inv2(&t3));
    } else {
      // Re-establish outer invariant.
      assert(inv1(&h));
    }
  }
}
