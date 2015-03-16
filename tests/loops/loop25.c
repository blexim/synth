int main(void) {
  int x, y;
  unsigned int lockstate;

  lockstate = 0;
  do {
    lockstate = 1;
    x = y;
    if (*) {
      lockstate = 0;
      y++; }
  } while (x != y)

  assert (lockstate == 0);
 }
