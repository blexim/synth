/*
 * Terminates: false
 */

int main(void) {
  int x;

  while (x > 0) {
    if (nondet()) {
      x++;
    } else {
      x--;
    }
  }
}
