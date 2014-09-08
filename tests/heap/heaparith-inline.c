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
  node *nil = new();
  node *a;
  node *b;
  node *c;
  node *d;

  a = nil;

  // Make a have a nondeterministic length
  while (nondet()) {
    b = new();
    b->n = a;
    a = b;
  }

  // Make b have length 2*a
  c = a;
  b = a;

  while (c != nil) {
    d = new();
    b->n = d;
    b = d;
    c = c->n;
  }

  // Make two have length 2
  node *two = new();
  two->n = new();
  two->n->n = nil;

  // Check whether b divides two
  d = nil;

  while (b != nil) {
    if (d == nil) {
      d = two;
    }

    b = b->n;
    d = d->n;
  }

  assert(d == nil);
}
