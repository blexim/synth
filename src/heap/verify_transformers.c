#include "heap.h"

int main(void) {
  abstract_heapt heap1, heap2;

  ptr_t x;
  ptr_t y;

  __CPROVER_assume(x < NPROG);
  __CPROVER_assume(y < NPROG);

  __CPROVER_assume(valid_abstract_heap(&heap1));
  __CPROVER_assume(is_minimal(&heap1));

  abstract_new(&heap1, &heap2, x);
  assert(valid_abstract_heap(&heap2));
  assert(is_minimal(&heap2));

  abstract_lookup(&heap1, &heap2, x, y);
  assert(valid_abstract_heap(&heap2));
  assert(is_minimal(&heap2));

  abstract_assign(&heap1, &heap2, x, y);
  assert(valid_abstract_heap(&heap2));
  assert(is_minimal(&heap2));

  abstract_update(&heap1, &heap2, x, y);
  assert(valid_abstract_heap(&heap2));
  assert(is_minimal(&heap2));
}
