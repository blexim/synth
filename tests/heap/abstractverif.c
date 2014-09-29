#include "heapabstract.h"

int main(void) {
  concrete_heapt heap1, heap2;
  abstract_heapt abs1, abs2;

  abstract(heap1, abs1);
  abstract(heap2, abs2);

  if (abstractions_equal(abs1, abs2) &&
      is_valid_heap(heap1) &&
      is_valid_heap(heap2)) {
    assert(heaps_isomorphic(heap1, heap2));
  }
}
