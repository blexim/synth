#include "heapabstract.h"

const word_t x = 1;
const word_t y = 2;

int tests = 0;
int passed = 0;

void test_assign(concrete_heapt *heap1) {
  concrete_heapt heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(heap1, &abs1);
  abstract_assign(x, y, &abs1, &abs2);

  concrete_assign(x, y, heap1, &heap2);
  abstract(&heap2, &abs3);

  printf("Concrete heap1:\n");
  print_concrete(heap1);

  printf("\nAbstract1:\n");
  print_abstract(&abs1);

  printf("\nExecuting x = y:\n");

  printf("\nAbstract result:\n");
  print_abstract(&abs2);

  printf("\nConcrete result:\n");
  print_concrete(&heap2);

  printf("\nAbstracted concrete:\n");
  print_abstract(&abs3);

  tests++;

  if (is_valid_heap(heap1) &&
      !abstractions_equal(&abs2, &abs3)) {
    printf("TEST FAILED\n");
  } else {
    passed++;
    printf("TEST SUCCEEDED\n");
  }
}

void test_assigns() {
  concrete_heapt heap1 = {
    .succ={ INF, 2, 1 }, .ptr={ 0, 1, 1 }
  };

  test_assign(&heap1);
}

void main() {
  test_assigns();

  printf("\n%d/%d tests passed\n", passed, tests);
}
