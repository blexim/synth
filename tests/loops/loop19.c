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
  int x = 1001;

  while (x > 0) {
    x -= 2;
  }

  assert(x >= 0);
}
