/*
 * This example illustrates a massive ballache:
 * we can encode arithmetic properties using just
 * pointer equality and loops.
 */

#include <stdlib.h>
#include <assert.h>

#define LEN 101

typedef struct node_t {
  struct node_t *n;
} node;

node *new() {
  return malloc(sizeof(node));
}

/*
 * Returns NULL iff len(b) divides len(a)
 */

node *divides(node *a, node *b) {
  node *c = NULL;

  while (a != NULL) {
    if (c == NULL) {
      c = b;
    }

    c = c->n;
    a = a->n;
  }

  return c;
}

node *add(node *a, node *b) {
  node *ret = a;

  while (b != NULL) {
    node *c = new();
    c->n = ret;
    ret = c;

    b = b->n;
  }

  return ret;
}

int main(void) {
  node *a = NULL;
  node *b;
  int i;

  for (i = 0; i < LEN; i++) {
    b = new();
    b->n = a;
    a = b;
  }


  b = add(a, a);

  node *two = new();
  two->n = new();
  two->n->n = NULL;

  assert(divides(b, two) == NULL);
}
