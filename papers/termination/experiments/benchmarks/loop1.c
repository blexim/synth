/*
 * Name:           loop1
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */

int main(void) {
  unsigned int x = nondet();

  while (x > 0) {
    x--;
  }
}
