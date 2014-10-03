int has_cycle(list l) {
  list p = l;
  list q = l;

  do {
    if (p != NULL) p = p->n;
    if (q != NULL) q = q->n;
    if (q != NULL) q = q->n;
  } while (p ! q && p != NULL && q != NULL);

  return p == q;
}
