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
         //is_path(heap, y, z) &&
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
    return z_null == 0 || z_null == y_null;
  } else {
    return z_null != 0 && z_null != y_null;
  }
}

int cond(abstract_heapt *heap) {
  return !is_null(heap, w);
}

int pre(abstract_heapt *init_heap, abstract_heapt *post) {
  *post = *init_heap;

  return is_path(init_heap, x, null_ptr) &&
         is_path(init_heap, y, null_ptr) &&
         !is_null(init_heap, y) &&
         alias(init_heap, z, y) &&
         alias(init_heap, w, x);
}

int body(abstract_heapt *pre_heap, abstract_heapt *post_heap) {
  abstract_heapt t1, t2;

  if (is_null(pre_heap, z)) {
    abstract_assign(pre_heap, &t1, z, y);
  } else {
    t1 = *pre_heap;
  }

  if (is_null(&t1, z)) {
    return 0;
  }

  abstract_lookup(&t1, &t2, z, z);

  if (is_null(&t2, w)) {
    return 0;
  }
  abstract_lookup(&t2, post_heap, w, w);

  return 1;
}
