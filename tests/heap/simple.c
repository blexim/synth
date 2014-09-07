int main(void) {
  node_t *x, *y;

  assume(len(x, NULL) == len(y, NULL));

  while (x != NULL && y != NULL) {
    x = x->n;
    y = y->n;
  }

  assert(x == NULL && y == NULL);
}
