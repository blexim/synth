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
  int x,y;

  y = 1;

  while (x > 0) {
    x = x-y;
  }
}
