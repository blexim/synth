int has_cycle(list l) {
  list p = l;
  list q = l;

  do {
    p = p->n;
    q = q->n;
    q = q->n;
  } while (p ! q && p != NULL && q != NULL);

  return p == q;
}
