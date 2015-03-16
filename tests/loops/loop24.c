/*
 * Danger invariant:
 *  x_0 = y_0 = nondet_0 = 0
 *  D(nondet0, x, y) = y == (x ? x : 1)
 *  R(nondet0, x, y) = x
 *  nondet(x, y) = x
 */
int main(void) {
  unsigned int i, c, a;

  i = 0;
  c = 0;

  while (i < 1000) {
    c = c+i;
    i++;
    
  }

  assert(a > 0);
}

