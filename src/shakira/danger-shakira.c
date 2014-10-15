#include "heap.h"

extern int pre(abstract_heapt *pre, abstract_heapt *post);
extern int cond(abstract_heapt *heap);
extern int body(abstract_heapt *pre, abstract_heapt *post);
extern int assertion(abstract_heapt *heap);
extern int init(abstract_heapt *heap);
extern int danger(abstract_heapt *heap);

extern word_t rank1(abstract_heapt *heap);
extern word_t rank2(abstract_heapt *heap);

void main(void) {
  abstract_heapt h, t1, t2;

  assert(NABSNODES >= (NLIVE*2) + 1);

  if (!valid_abstract_heap(&h)) {
    return;
  }

  // Base.
  if (init(&h) &&
      pre(&h, &t1)) {
    assert(danger(&t1));
  }

  if (danger(&h)) {
    word_t cond_holds = cond(&h);
    word_t body_safe = body(&h, &t2);

    if (cond_holds && body_safe) {
      // Induction.
      assert(danger(&t2));

      // Bounded ranking function.
      word_t r1 = rank1(&h);
      word_t r1_ = rank1(&t2);

      word_t r2 = rank2(&h);
      word_t r2_ = rank2(&t2);

      assert(r1 > 0 || r2 > 0);

      // Ranking function decreases.
      assert(r1 >= r1_);
      if (r1 == r1_) {
        assert(r2 > r2_);
      }
    } else if (!cond_holds) {
        // Property.
        assert(!assertion(&h));
    } else {
      // Assertion violation in the body -- no worries.
    }
  }
}
