int main(void) {
  int x, y;

  x = 0;
  y = 0;

  while (nondet()) {
    x++;
    y++;
  }

  assert(x == y);
}
