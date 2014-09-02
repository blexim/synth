/*
 * Name:           loop3
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    true
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 */

int main(void) {
  unsigned int x;
  int y;
  
  y = 1;

  while (x > 0) {
    x -= y;
  }
}
