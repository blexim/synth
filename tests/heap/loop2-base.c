#include "heaplib.h"

int main(void) {
  node_t *x, *y;

  assume(y == x->n);

  while (true) {
    assert(y == x->n);

    y = y->n;
    x = x->n;
  }
}
