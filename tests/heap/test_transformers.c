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

void test_lookup(concrete_heapt *heap1) {
  concrete_heapt heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(heap1, &abs1);
  abstract_lookup(x, y, &abs1, &abs2);

  concrete_lookup(x, y, heap1, &heap2);
  abstract(&heap2, &abs3);

  printf("Concrete heap1:\n");
  print_concrete(heap1);

  printf("\nAbstract1:\n");
  print_abstract(&abs1);

  printf("\nExecuting x = y->n:\n");

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

void test_lookups() {
#if NNODES==3
  concrete_heapt heap1 = {
    .succ={ INF, 0, 0 }, .ptr={ 0, 0, 2 }
  };
  test_lookup(&heap1);

  concrete_heapt heap2 = {
    .succ={ INF, 1, 0 }, .ptr={ 0, 2, 2 }
  };
  test_lookup(&heap2);

  concrete_heapt heap3 = {
    .succ={ INF, 2, 0 }, .ptr={ 0, 0, 1 }
  };
  test_lookup(&heap3);

  concrete_heapt heap4 = {
    .succ={ INF, 1, 0 }, .ptr={ 0, 0, 1 }
  };
  test_lookup(&heap4);

  concrete_heapt heap5 = {
    .succ={ INF, 2, 2 }, .ptr={ 0, 2, 1 }
  };
  test_lookup(&heap5);
#elif NNODES==4
  concrete_heapt heap6 = {
    .succ={ INF, 2, 2, 0 }, .ptr={ 0, 2, 2, 1 }
  };
  test_lookup(&heap6);

  concrete_heapt heap7 = {
    .succ={ INF, 2, 3, 1 }, .ptr={ 0, 1, 1, 0 }
  };
  test_lookup(&heap7);

  concrete_heapt heap8 = {
    .succ={ INF, 3, 1, 1 }, .ptr={ 0, 0, 3, 2 }
  };
  test_lookup(&heap8);

  concrete_heapt heap9 = {
    .succ={ INF, 2, 1, 2 }, .ptr={ 0, 2, 1, 3 }
  };
  test_lookup(&heap9);
#elif NNODES==5
  concrete_heapt heap9 = {
    .succ={ INF, 2, 3, 2, 3 }, .ptr={ 0, 4, 4, 1, 4 }
  };
  test_lookup(&heap9);

  concrete_heapt heap10 = {
    .succ={ INF, 2, 4, 1, 2 }, .ptr={ 0, 2, 3, 4, 4 }
  };
  test_lookup(&heap10);
#endif
}

void test_update(concrete_heapt *heap1) {
  concrete_heapt heap2;
  abstract_heapt abs1, abs2, abs3;

  abstract(heap1, &abs1);
  abstract_update(x, y, &abs1, &abs2);

  concrete_update(x, y, heap1, &heap2);
  abstract(&heap2, &abs3);

  tests++;

  if (!is_valid_heap(heap1) ||
      abstractions_equal(&abs2, &abs3)) {
    passed++;
    //printf("TEST SUCCEEDED\n");
    return;
  }

  printf("\n\n               TEST %d FAILED:\n", tests);

  printf("Concrete heap1:\n");
  print_concrete(heap1);

  printf("\nAbstract1:\n");
  print_abstract(&abs1);

  printf("\nExecuting x->n = y:\n");

  printf("\nAbstract result:\n");
  print_abstract(&abs2);

  printf("\nConcrete result:\n");
  print_concrete(&heap2);

  printf("\nAbstracted concrete:\n");
  print_abstract(&abs3);
}

void test_updates() {
#if NNODES==3
  concrete_heapt heap1 = {
    .succ={ INF, 1, 1 }, .ptr={ 0, 2, 0 }
  };
  test_update(&heap1);

  concrete_heapt heap2 = {
    .succ={ INF, 2, 2 }, .ptr={ 0, 2, 0 }
  };
  test_update(&heap2);

  concrete_heapt heap3 = {
    .succ={ INF, 1, 1 }, .ptr={ 0, 1, 1 }
  };
  test_update(&heap3);

  concrete_heapt heap4 = {
    .succ={ INF, 1, 0 }, .ptr={ 0, 2, 2 }
  };
  test_update(&heap4);

  concrete_heapt heap5 = {
    .succ={ INF, 0, 1 }, .ptr={ 0, 1, 2 }
  };
  test_update(&heap5);

  concrete_heapt heap6 = {
    .succ={ INF, 1, 1 }, .ptr={ 0, 2, 1 }
  };
  test_update(&heap6);
#elif NNODES==4
  concrete_heapt heap2 = {
     .succ={ INF, 3, 3, 0 }, .ptr={ 0, 3, 2, 1 }
  };
  test_update(&heap2);

  concrete_heapt heap3 = {
    .succ={ INF, 0, 3, 1 }, .ptr={ 0, 1, 1, 2 }
  };
  test_update(&heap3);

  concrete_heapt heap4 = {
    .succ={ INF, 2, 1, 3 }, .ptr={ 0, 2, 2, 1 }
  };
  test_update(&heap4);

  concrete_heapt heap5 = {
    .succ={ INF, 3, 1, 2 }, .ptr={ 0, 3, 1, 2 }
  };
  test_update(&heap5);

  concrete_heapt heap6 = {
    .succ={ INF, 2, 3, 1 }, .ptr={ 0, 2, 3, 1 }
  };
  test_update(&heap6);

  concrete_heapt heap7 = {
    .succ={ INF, 2, 3, 2 }, .ptr={ 0, 2, 1, 3 }
  };
  test_update(&heap7);

  concrete_heapt heap8 = {
    .succ={ INF, 3, 3, 1 }, .ptr={ 0, 1, 2, 3 }
  };
  test_update(&heap8);

  concrete_heapt heap9 = {
    .succ={ INF, 2, 2, 1 }, .ptr={ 0, 3, 1, 2 }
  };
  test_update(&heap9);

  concrete_heapt heap10 = {
    .succ={ INF, 2, 2, 1 }, .ptr={ 0, 2, 1, 3 }
  };
  test_update(&heap10);

  concrete_heapt heap11 = {
    .succ={ INF, 2, 1, 1 }, .ptr={ 0, 3, 1, 2 }
  };
  test_update(&heap11);

  concrete_heapt heap12 = {
    .succ={ INF, 2, 1, 2 }, .ptr={ 0, 2, 1, 3 }
  };
  test_update(&heap12);
#elif NNODES==5
  concrete_heapt heap9 = {
    .succ={ INF, 4, 4, 1, 1 }, .ptr={ 0, 4, 2, 3, 1 }
  };
  test_update(&heap9);

  concrete_heapt heap10 = {
    .succ={ INF, 4, 1, 1, 3 }, .ptr={ 0, 4, 3, 2, 1 }
  };
  test_update(&heap10);

  concrete_heapt heap11 = {
    .succ={ INF, 3, 4, 2, 3 }, .ptr={ 0, 2, 1, 3, 4 }
  };
  test_update(&heap11);

  concrete_heapt heap12 = {
    .succ={ INF, 4, 1, 4, 2 }, .ptr={ 0, 2, 1, 3, 4 }
  };
  test_update(&heap12);
#endif
}

void main() {
  //test_assigns();
  //test_lookups();
  test_updates();

  printf("\n%d/%d tests passed\n", passed, tests);
}
