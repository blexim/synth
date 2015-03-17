/*
 * An unsafe loop.
 *
 * Danger invariant:
 *
 *  x_0 = 1001
 *  D(x) = x & 1
 *  R(x) = x
 */
int main(void) {
  int x;

  if (x < 100 || x > 200) {
    return 0;
  }

  while (x > 0) {
    x -= 2;
  }

  assert(x >= 0);
}
