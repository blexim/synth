/*
 * Terminates: false
 */

int main(void) {
  int x;

  while (x > 0) {
    x = (x + 1) & x;
  }
}
