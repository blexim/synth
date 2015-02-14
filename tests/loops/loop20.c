int main(void) {
  unsigned int x, y;

  x = 0;
  y = 0;

  while (x < 10) {
    x++;

    if (nondet()) {
      y++;
    }
  }

  assert(x != y);
}

