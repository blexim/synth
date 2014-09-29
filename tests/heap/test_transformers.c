#include "heapabstract.h"

int main(void) {
  word_t x = 1;
  word_t y = 2;

  concrete_heapt heap1 = {
    .succ={ INF, 1, 0 }, .ptr={ 0, 1, 1 }
  };
  concrete_heapt heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(&heap1, &abs1);
  abstract_assign(x, y, &abs1, &abs2);

  concrete_assign(x, y, &heap1, &heap2);
  abstract(&heap2, &abs3);

  printf("Concrete heap1:\n");
  print_concrete(&heap1);

  printf("\nAbstract1:\n");
  print_abstract(&abs1);

  printf("\nExecuting x = y:\n");

  printf("\nAbstract result:\n");
  print_abstract(&abs2);

  printf("\nConcrete result:\n");
  print_concrete(&heap2);

  printf("\nAbstracted concrete:\n");
  print_abstract(&abs3);

  if (is_valid_heap(&heap1)) {
    assert(abstractions_equal(&abs2, &abs3));
  }
}

