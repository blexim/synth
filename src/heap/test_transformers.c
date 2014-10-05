#include "heap.h"

int main(void) {
  abstract_heapt heap1 = {
    .succ={ 0, 1, 1, 2, 3 }, .dist={ 0, 1, 4, 1, 1 }, .ptr={ 0, 1 },
          .nnodes=2
  };
  ptr_t x = 1;
  ptr_t y = 0;
  abstract_heapt heap2;


  //__CPROVER_assume(x < NPROG);
  //__CPROVER_assume(y < NPROG);

  //__CPROVER_assume(valid_abstract_heap(&heap1));

  abstract_new(&heap1, &heap2, x);

  print_abstract_heap(&heap1);
  printf("\nx = new();\n");
  print_abstract_heap(&heap2);

  printf("Heap 1 is valid: %d\n", valid_abstract_heap(&heap1));
  printf("Heap 2 is valid: %d\n", valid_abstract_heap(&heap2));


  //abstract_lookup(&heap1, &heap2, x, y);
  //assert(valid_abstract_heap(&heap2));

  //abstract_assign(&heap1, &heap2, x, y);
  //assert(valid_abstract_heap(&heap2));

  //abstract_update(&heap1, &heap2, x, y);
  //assert(valid_abstract_heap(&heap2));
}
