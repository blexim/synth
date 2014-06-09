/*
 * Name:           loop2
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */

int main(void) {
  unsigned int x = nondet();
  unsigned int N = nondet();

  while (x < N) {
    x++;
  }
}
