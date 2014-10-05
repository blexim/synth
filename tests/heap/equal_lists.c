#include "heap.h"

/*
 * assume(len(x, null) == len(y, null));
 *
 * while (x != null && y != null) {
 *   assert(y != null);
 *
 *   x = x->n;
 *   y = y->n;
 * }
 */

ptr_t x = 1;
ptr_t y = 2;

int cond(heap_factst *facts) {
  return !alias(facts, x, null_ptr) && !alias(facts, y, null_ptr);
}

int inv(heap_factst *facts) {
  return path_len(facts, x, null_ptr) == path_len(facts, y, null_ptr);
}

int body(abstract_heapt *pre,
         abstract_heapt *post) {
  abstract_heapt tmp;

  abstract_lookup(pre, &tmp, x, x);
  abstract_lookup(&tmp, post, y, y);
}

int main(void) {
  abstract_heapt heap1, heap2, heap3, post_heap;
  heap_factst pre_facts, post_facts;

  __CPROVER_assume(valid_abstract_heap(&heap1));
  consequences(&heap1, &pre_facts);
  __CPROVER_assume(inv(&pre_facts));

  body(&heap1, &post_heap);
  consequences(&post_heap, &post_facts);
  assert(inv(&post_facts));
}
