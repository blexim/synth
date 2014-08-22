#include "heaplib.h"

int main(void) {
  node_t *x, *y;

  assume(path(x, y));

  while (x != y) {
    assert(x != NULL);
    x = x->n;
  }
}
