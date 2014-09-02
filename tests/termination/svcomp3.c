/*
 * Name:           SVCOMP-Ben-Amram-2010LMCS
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  unk
 * Terminates:     true
 * Bibtex:         BA:mcs
 */

int main(void)
{
  int x, y, z;

  while (x > 0 && y > 0 && z > 0) {
    if (y > x) {
      y = z;
      x = nondet();
      z = x - 1;
    } else {
      z = z - 1;
      x = nondet();
      y = x - 1;
    }
  }
}
