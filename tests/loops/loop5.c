int main(void) {
  int i, j, x, y;

  x = i;
  y = j;

  while (x != 0) {
    x--;
    y--;
  }

  if (i == j) {
    assert(y == 0);
  }
}
