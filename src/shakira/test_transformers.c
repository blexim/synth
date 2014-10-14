#include "heap.h"

int main(void) {
  abstract_heapt heap1 = {
    .succ={ 0, 4, 3, 5, 6, 3, 6 }, .dist={ 0, 9, 1, 9, 4, 9, 1 }, .ptr={ 0, 1, 4 },
        .nnodes=0
  };
  ptr_t x = 1;
  ptr_t y = 2;
  abstract_heapt heap2;


  //__CPROVER_assume(x < NPROG);
  //__CPROVER_assume(y < NPROG);

  //__CPROVER_assume(valid_abstract_heap(&heap1));

  abstract_lookup(&heap1, &heap2, x, y);

  print_abstract_heap(&heap1);
  printf("\nx = y->n;\n");
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
