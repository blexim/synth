int main(void) {
  int a, b, x, y;

  x = a;
  y = b;

  while (x > 0 && y > 0) {
    if (nondet()) {
      x--;
      y = nondet();
    } else {
      y--;
    }
  }
}
