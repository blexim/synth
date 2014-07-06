/*
 * Name:           loop8
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    true
 * Float:          true
 * Bitvector:      true
 * Lexicographic:  1
 * Terminates:     true
 */

int main(void) {
  float f = 100.0;

  while (f > 0.0) {
    f *= 0.5;
  }
}
