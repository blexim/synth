int main(void) {
  unsigned int x;

  x = 0;

  while (x < 100) {
    if (x < 51) {
      x++;
    } else {
      x += 2;
    }
  }

  assert(!(x % 2));
}
