#include "heapabstract.h"

int main(void) {
  unsigned int x = 1;
  unsigned int y = 2;

  concrete_heapt heap1, heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(heap1, abs1);
  abstract_assign(x, y, abs1, abs2);

  concrete_assign(x, y, heap1, heap2);
  abstract(heap2, abs3);

  if (is_valid_heap(heap1)) {
    assert(abstractions_equal(abs2, abs3));
  }
}

