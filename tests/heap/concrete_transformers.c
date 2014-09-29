#include "heapabstract.h"

void concrete_assign(word_t x,
                     word_t y,
                     concrete_heapt pre,
                     concrete_heapt post) {
  int i;

  for (i = 0; i < NMATRIX; i++) {
    post[i] = pre[i];
  }

  post[ptr(x)] = pre[ptr(y)];
}
