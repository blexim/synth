int main(void) {
  int x, y;
  unsigned int lockstate;

  lockstate = 0;

  lockstate = 1;
  x = y;

  if (nondet()) {
    lockstate = 0;
    y++;
  }

  while (x != y) {
    lockstate = 1;
    x = y;

    if (nondet()) {
      lockstate = 0;
      y++;
    }
  }

  assert (lockstate == 0);
}
