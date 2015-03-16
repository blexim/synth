/*
 * An unsafe loop, modelling a check for a buffer overflow.
 *
 * Danger invariant:
 *
 *  x_0 = 3221225472
 *  i_0 = len_0 = 0
 *  D(x, len, i) = i == 0 && x != 0 && len == 0
 *  R(x, len, i) = true
 */

int main(void) {
  unsigned int x;
  unsigned int len;
  unsigned int i;

  len = x * 4;
  i = 0;

  while (i * 4 < len && i < x) {
    i++;
  }

  assert(i * 4 < len || i >= x);
}
