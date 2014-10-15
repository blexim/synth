#include "heap.h"
#include "state.h"

extern int pre(statet *pre, statet *post);
extern int cond(statet *staet);
extern int body(statet *pre, statet *post);
extern int assertion(statet *state);
extern int inv(statet *state);

void main(void) {
  statet h, t1, t2;

  assert(NABSNODES >= (NLIVE*2) + 1);

  if (!valid_abstract_heap(&(h.heap))) {
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
