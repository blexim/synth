#include "heap.h"

extern int pre1(statet *heap, statet *post);
extern int pre2(statet *heap, statet *post);

extern int cond1(statet *heap);
extern int cond2(statet *heap);

extern int body2(statet *pre, statet *post);

extern int assertion(statet *heap);

extern int inv1(statet *heap);
extern int inv2(statet *heap);

void main(void) {
  statet h, t1, t2, t3;

  //assert(NABSNODES >= (NLIVE*2) + 1);

  if (!valid_abstract_heap(&(h.heap))) {
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
