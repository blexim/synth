/*
 * Name:           SVCOMP-Avery2006FLOPS
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/flops/Avery06
 */

int main(void)
{
  int x, y, z, i;

  z = 0;
  i = x;

  if (y <= 0 || x <= 0) {
    return 1;
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
