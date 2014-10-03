#include "heapabstract.h"
#include "heap_axioms.h"

int axioms(abstract_heapt *heap) {
  return alias_axioms(heap) &&
         path_axioms(heap) &&
         null_axioms(heap) &&
         cycle_axioms(heap);
}

word_t x = 1;
word_t y = 2;

int main(void) {
  abstract_heapt abs1, t, abs2;

  __CPROVER_assume(axioms(&abs1));

  abstract_new(x, &abs1, &t);

  __CPROVER_assume(abstractions_equal(&t, &abs2));

  assert(axioms(&abs2));
}
