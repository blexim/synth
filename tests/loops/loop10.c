int main() {
  int x;
  int i = 0xffffff;

  while (i > 0) {
    i--;
    x += 2;
  }

  assert(!(x % 2));
}
