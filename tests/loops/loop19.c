int main(void) {
  int x = 1001;

  while (x > 0) {
    x -= 2;
  }

  assert(x >= 0);
}
