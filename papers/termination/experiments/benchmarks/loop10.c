/*
 * Name:           loop10
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      true
 * Lexicographic:  1
 */

int main(void) {
  unsigned int x = nondet();

  while (x > 0) {
    x++;
  }
}
