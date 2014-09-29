#include "heapabstract.h"

int check(concrete_heapt *heap1, concrete_heapt *heap2) {
  abstract_heapt abs1, abs2;

  if (!is_valid_heap(heap1) || !is_valid_heap(heap2)) {
    return 1;
  }

  if (heaps_isomorphic(heap1, heap2)) {
    return 1;
  }

  abstract(heap1, &abs1);
  abstract(heap2, &abs2);

  if (!abstractions_equal(&abs1, &abs2)) {
    return 1;
  }

  return 0;
}

int main(void) {
  concrete_heapt heap1, heap2;

  assert(check(&heap1, &heap2));
}

