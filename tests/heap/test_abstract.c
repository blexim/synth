#include "heap.h"

const word_t x = 1;
const word_t y = 2;
const word_t z = 3;

int main(void) {
  abstract_heapt heap1, heap2;
  heap_factst facts;

  init_abstract_heap(&heap1);
  consequences(&heap1, &facts);

  print_abstract_heap(&heap1);
  print_facts(&facts);

  printf("\nx = new();\n");
  abstract_new(&heap1, &heap2, x);
  consequences(&heap2, &facts);

  print_abstract_heap(&heap2);
  print_facts(&facts);

  printf("\ny = new(); x->n = y\n");
  abstract_new(&heap2, &heap1, y);
  abstract_update(&heap1, &heap2, x, y);
  consequences(&heap2, &facts);

  print_abstract_heap(&heap2);
  print_facts(&facts);

  printf("\nz = new(); z->n = y\n");
  abstract_new(&heap2, &heap1, z);
  abstract_update(&heap1, &heap2, z, y);
  consequences(&heap2, &facts);

  print_abstract_heap(&heap2);
  print_facts(&facts);

  printf("\ny = z;\n");
  abstract_assign(&heap2, &heap1, y, z);
  consequences(&heap1, &facts);

  print_abstract_heap(&heap1);
  print_facts(&facts);

  printf("\ny = y->n;\n");
  abstract_lookup(&heap1, &heap2, y, y);
  consequences(&heap2, &facts);

  print_abstract_heap(&heap2);
  print_facts(&facts);

  printf("\nx = new();\n");
  abstract_new(&heap2, &heap1, x);
  consequences(&heap1, &facts);

  print_abstract_heap(&heap1);
  print_facts(&facts);
}
