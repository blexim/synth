int main(void) {
  int x = 100;

  while (x != 0) {
    if (x < 0) {
      x = -x - 1;
    } else {
      x = -x + 1;
    }
  }
}
