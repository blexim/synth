#ifndef WORDMASK
 #define WORDMASK 0xffffffff
#endif

/*
 * Danger invariant:
 *  x_0 = y_0 = nondet_0 = 0
 *  D(nondet0, x, y) = y == (x ? x : 1)
 *  R(nondet0, x, y) = -x
 *  nondet(x, y) = x
 */
int main(void) {
  unsigned int x, y;

  x = 0;
  y = 1;

  while (x < (1000000 & WORDMASK)) {
    x++;

    if (nondet()) {
      y++;
    }
  }

  assert(x != y);
}

