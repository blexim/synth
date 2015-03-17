int main(void) {
  unsigned int x;
  unsigned int y;

  y = x + 1;

  while (x < 100) {
    x++;
    y++;
  }

  assert(x == y);
}
