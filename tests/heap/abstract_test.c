#include "heapabstract.h"

int main(void) {
  concrete_heapt heap1 =
  {
    .succ={ INF, 1, 0 }, .ptr={ 0, 1, 1 }
  };
  concrete_heapt heap2 =
  {
    .succ={ INF, 2, 2 }, .ptr={ 0, 2, 2 }
  };

  abstract_heapt abs1;
  abstract_heapt abs2;

  abstract(&heap1, &abs1);
  abstract(&heap2, &abs2);

  printf("Concrete1:\n");
  print_concrete(&heap1);
  printf("\nAbstract1:\n");
  print_abstract(&abs1);

  printf("\nConcrete2:\n");
  print_concrete(&heap2);
  printf("\nAbstract2:\n");
  print_abstract(&abs2);

  if (is_valid_heap(&heap1) && is_valid_heap(&heap2) &&
      !heaps_isomorphic(&heap1, &heap2) &&
      abstractions_equal(&abs1, &abs2)) {
    printf("TEST FAILED\n");
  } else {
    printf("TEST SUCCEEDED\n");
  }
}
