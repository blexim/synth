/*
 * Name:           loop6
 * Linear-program: false
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 */

int main(void) {
  unsigned int x;

  while (x > 0) {
    x = (x - 1) & x;
  }
}
