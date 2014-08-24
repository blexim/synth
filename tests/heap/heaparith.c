/*
 * This example illustrates a massive ballache:
 * we can encode arithmetic properties using just
 * pointer equality and loops.
 */

/*
 * Returns NULL iff len(b) divides len(a)
 */

node *divides(node *a, node *b) {
  node *c = b;

  [c != NULL ==> a != NULL]

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

int f(node *a) {
  assume(path(a, NULL));

  node *b = add(a, a);

  node *two = new();
  two->n = new();
  two->n->n = NULL;

  assert(divides(b, two) == NULL);
}
