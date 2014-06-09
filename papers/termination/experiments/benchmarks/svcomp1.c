/*
 * Name:           SVCOMP-Avery2006FLOPS
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */

int main(void)
{
  int x, y, z, i;

  x = nondet();
  y = nondet();
  z = 0;
  i = x;

  if (y <= 0 || x <= 0) {
    return 0;
  }

  while (i > 0) {
    i--;
    z++;
  }

  while (i < y) {
    i++;
    z--;
  }
}
