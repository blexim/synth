#include "heapabstract.h"

void copy_concrete(concrete_heapt *pre,
                   concrete_heapt *post) {
  int i;

  for (i = 0; i < NNODES; i++) {
    post->succ[i] = pre->succ[i];
    post->ptr[i] = pre->ptr[i];
  }
}

void concrete_assign(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post) {
  //word_t px = pre->ptr[x];
  //__CPROVER_assume(x != 0);

  copy_concrete(pre, post);
  post->ptr[x] = pre->ptr[y];
}

void concrete_lookup(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post) {
  word_t py = pre->ptr[y];
  word_t yn = pre->succ[py];

  __CPROVER_assume(py != 0);

  copy_concrete(pre, post);
  post->ptr[x] = yn;
}

void concrete_update(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post) {
  word_t py = pre->ptr[y];
  word_t px = pre->ptr[x];

  __CPROVER_assume(px != 0);

  copy_concrete(pre, post);
  post->succ[px] = py;
}

void concrete_new(word_t x,
		  concrete_heapt *pre,
		  concrete_heapt *post) {
  word_t new_node = 0;
  word_t n;

  /* search for an anonymous node without incoming edges and whose successor is null */
  for(n = 0; n < NNODES; n++)
    if(!named_ptr(n, pre) && pre->succ[n] == 0 && !has_predecessor(pre, n))
      new_node = n;

  // we'll use this node as the new allocated node
  __CPROVER_assume(new_node != 0);

  copy_concrete(pre, post);
  post->ptr[x] = new_node;
}
