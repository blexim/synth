#include "heapabstract.h"

int main(void) {
  abstract_heapt heap1, heap2;

  if (is_valid_abstract_heap(&heap1)) {
    abstract_lookup(1, 1, &heap1, &heap2);
    assert(is_valid_abstract_heap(&heap2));

    abstract_lookup(1, 2, &heap1, &heap2);
    assert(is_valid_heap(&heap2));
  }
}
