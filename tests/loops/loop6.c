int main(void) {
  int x, y;

  x = 0;
  y = 0;

  while (nondet() && y < 0xffffff) {
    if (nondet()) {
      x++;
      y += 100;
    } else {
      if (x >= 4) {
        x++;
        y++;
      }
    }
  }

  assert(x <= y && y <= 100 * x);
}
