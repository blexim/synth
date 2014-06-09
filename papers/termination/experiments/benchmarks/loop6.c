/*
 * Name:           loop6
 * Linear-program: false
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */

int main(void) {
  unsigned int x = nondet();

  while (x > 0) {
    x = (x - 1) & x;
  }
}
