#include "heap.h"

/*
 * List x, y;
 *
 * assume(path_len(x, null) == path_len(y, null))
 *
 * while (x != null) {
 *   x = x->n;
 *   y = y->n;
 * }
 * 
 * assert(y == null);
 *
 * Prove safety using invariant:
 *  path_len(y, null) == path_len(x, null)
 */

const ptr_t x = 1;
const ptr_t y = 2;

int inv(heap_factst *facts) {
  return path_len(*facts, y, null_ptr) == path_len(*facts, x, null_ptr);
}

int cond(heap_factst *facts) {
  return !alias(*facts, x, null_ptr);
}

int assertion(heap_factst *facts) {
  return alias(*facts, y, null_ptr);
}

int main(void) {
  abstract_heapt pre_heap, post_heap;
  abstract_heapt t1, t2;
  heap_factst f1, f2, f3;

  __CPROVER_assume(valid_abstract_heap(&pre_heap));
  consequences(&pre_heap, &f1);
  __CPROVER_assume(inv(&f1));
  __CPROVER_assume(cond(&f1));

  abstract_lookup(&pre_heap, &t1, x, x);
  abstract_lookup(&t1, &t2, y, y);

  consequences(&t2, &f2);
  assert(inv(&f2));

  __CPROVER_assume(valid_abstract_heap(&post_heap));
  consequences(&post_heap, &f3);
  __CPROVER_assume(inv(&f3));
  __CPROVER_assume(!cond(&f3));

  assert(assertion(&f3));
}
