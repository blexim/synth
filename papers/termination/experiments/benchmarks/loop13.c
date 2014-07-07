/*
 * Terminates: false
 */

int main(void) {
  int x;
  int y;

  y = 1;

  while (x > 0) {
    if (nondet()) {
      x *= y;
    } else {
      x *= -y;
    }

    y = -y;
  }
}
