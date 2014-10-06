#include "heap.h"

/*
 * int divides(List x, List y) {
 *   assume(path(x, null) && path(y, null));
 *
 *   List z = y;
 *   List w = x;
 *
 *   while (w != null) {
 *     if (z == null) {
 *       z = y;
 *     }
 *
 *     z = z->n; w = w->n;
 *   }
 *
 *   return z == null;
 * }
 */

const ptr_t x = 1;
const ptr_t y = 2;
const ptr_t z = 3;
const ptr_t w = 4;

int inv(heap_factst *facts) {
  return is_path(*facts, x, null_ptr) &&
         is_path(*facts, z, null_ptr) &&
         is_path(*facts, y, null_ptr) &&
         is_path(*facts, y, null_ptr) &&
         (s_add(path_len(*facts, x, w), path_len(*facts, z, null_ptr)) %
          path_len(*facts, y, null_ptr)) == 0;
}

int assertion(heap_factst *facts) {
  if (path_len(*facts, x, null_ptr) % path_len(*facts, y, null_ptr) == 0) {
    return alias(*facts, z, null_ptr);
  } else {
    return !alias(*facts, z, null_ptr);
  }
}

int cond(heap_factst *facts) {
  return !alias(*facts, w, null_ptr);
}

int main(void) {
  abstract_heapt init_heap, pre_heap, post_heap;
  abstract_heapt t1, t2, t3;

  heap_factst f1, f2, f3;

  // Base case.
  __CPROVER_assume(valid_abstract_heap(&init_heap));
  consequences(&init_heap, &f1);

  __CPROVER_assume(path(f1, x, null_ptr));
  __CPROVER_assume(path(f1, y, null_ptr));
  __CPROVER_assume(alias(f1, z, y));
  __CPROVER_assume(alias(f1, w, x));

  assert(inv(&f1));

  // Induction.
  __CPROVER_assume(valid_abstract_heap(&pre_heap));
  consequences(&pre_heap, &f2);

  __CPROVER_assume(inv(&f2));
  __CPROVER_assume(cond(&f2));

  if (alias(f2, z, null_ptr)) {
    abstract_assign(&pre_heap, &t1, z, y);
  } else {
    t1 = pre_heap;
  }

  abstract_lookup(&t1, &t2, z, z);
  abstract_lookup(&t2, &t3, w, w);

  consequences(&t3, &f2);

  assert(inv(&f2));

  // Conclusion.
  __CPROVER_assume(valid_abstract_heap(&post_heap));
  consequences(&post_heap, &f3);

  __CPROVER_assume(inv(&f3));
  __CPROVER_assume(!cond(&f3));
  assert(assertion(&f3));
}
