/*
 * Name:           loop49
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  ?
 * Source:         -
 * Ranking function: |x|
 * Terminates:     false
 */


int main(void) {
  int x;

  while (x != 0) {
    x = x - nondet();
  }
}
