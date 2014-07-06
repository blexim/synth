/*
 * Name:           loop47
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  ?
 * Source:         -
 * Ranking function: |x|
 * Terminates:     true
 */

int main(void) {
  int x;

  while (x != 0) {
    x = -x/2;
  }
}
