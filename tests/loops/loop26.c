int main(void) {
  unsigned int x;

  x = 0;

  while (x < 1000) {
    if (x < 501) {
      x++;
    } else {
      x += 2;
    }
  }

  assert(!(x % 2));
}
