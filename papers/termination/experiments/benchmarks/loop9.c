/*
 * Name:           loop9
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */

int main(void) {
  int x = 2147483648;

  while (x != 0) {
    if (x < 0) {
      x = -x - 1;
    } else {
      x = -x + 1;
    }
  }
}
