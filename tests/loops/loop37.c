int main(void) {
  unsigned int x;
  unsigned int y;

  x = 0;

  while (x < 99) {
    if (y % 2 == 0) {
      x++;
    } else {
      x += 2;
    }
  }

  assert((x % 2) == (y % 2));
}
