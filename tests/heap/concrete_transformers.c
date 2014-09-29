#include "heapabstract.h"

void concrete_assign(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post) {
  int i;

  for (i = 0; i < NNODES; i++) {
    post->succ[i] = pre->succ[i];
    post->ptr[i] = pre->ptr[i];
  }

  post->ptr[x] = pre->ptr[y];
}
