#include "heapabstract.h"

int main(void) {
  word_t x = 1;
  word_t y = 2;

  concrete_heapt heap1 = {{ INF, 0, 2}, { 0, 0, 1 }};
  concrete_heapt heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(&heap1, &abs1);
  abstract_assign(x, y, &abs1, &abs2);

  concrete_assign(x, y, &heap1, &heap2);
  abstract(&heap2, &abs3);

  if (is_valid_heap(&heap1)) {
    assert(abstractions_equal(&abs2, &abs3));
  }
}

