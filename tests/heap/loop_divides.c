#include "heap.h"

/*
 * int divides(List x, List y) {
 *   assume(path(x, null) && path(y, null) && y != null);
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

int inv(abstract_heapt *heap) {
  word_t x_null = path_len(heap, x, null_ptr);
  word_t z_null = path_len(heap, z, null_ptr);
  //word_t w_null = path_len(heap, w, null_ptr);
  word_t y_null = path_len(heap, y, null_ptr);
  word_t x_w = path_len(heap, x, w);

  return x_null != INF &&
         z_null != INF &&
         x_w != INF &&
         y_null != INF &&
         y_null != 0 &&
         (s_add(x_w, z_null) % y_null == 0);
}

int assertion(abstract_heapt *heap) {
  word_t x_null = path_len(heap, x, null_ptr);
  word_t y_null = path_len(heap, y, null_ptr);
  word_t z_null = path_len(heap, z, null_ptr);

  if (x_null % y_null == 0) {
    return z_null == 0;
  } else {
    return z_null != 0;
  }
}

int cond(abstract_heapt *heap) {
  return !alias(heap, w, null_ptr);
}

int main(void) {
  abstract_heapt init_heap, pre_heap, post_heap;
  abstract_heapt t1, t2, t3;

#define phase 1

#if phase==1
  // Base case.
  __CPROVER_assume(valid_abstract_heap(&init_heap));

  __CPROVER_assume(is_path(&init_heap, x, null_ptr));
  __CPROVER_assume(is_path(&init_heap, y, null_ptr));
  __CPROVER_assume(!alias(&init_heap, y, null_ptr));
  __CPROVER_assume(alias(&init_heap, z, y));
  __CPROVER_assume(alias(&init_heap, w, x));

  assert(inv(&init_heap));
#elif phase==2
  // Induction.
  __CPROVER_assume(valid_abstract_heap(&pre_heap));

  __CPROVER_assume(inv(&pre_heap));
  __CPROVER_assume(cond(&pre_heap));

  if (alias(&pre_heap, z, null_ptr)) {
    abstract_assign(&pre_heap, &t1, z, y);
  } else {
    t1 = pre_heap;
  }

  abstract_lookup(&t1, &t2, z, z);
  abstract_lookup(&t2, &t3, w, w);

  assert(inv(&t3));
#else
  // Conclusion.
  __CPROVER_assume(valid_abstract_heap(&post_heap));

  __CPROVER_assume(inv(&post_heap));
  __CPROVER_assume(!cond(&post_heap));
  assert(assertion(&post_heap));
#endif
}
