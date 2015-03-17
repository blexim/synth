/*
 * Danger invariant:
 *  x_0 = y_0 = nondet_0 = 0
 *  D(nondet0, x, y) = x == y
 *  R(nondet0, x, y) = -x
 *  nondet(x, y) = 1
 */
int main(void) {
  unsigned int x, y;

  x = 0;
  y = 0;

  while (x < (1000003 & WORDMASK)) {
    if (nondet()) {
      x++;
    }

    if (nondet()) {
      y++;
    }
  }

  assert(x != y);
}

