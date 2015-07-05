
#ifndef WORDMASK
 #define WORDMASK 0xffffffff
#endif

int main(void) {
  unsigned int x = 1;
  unsigned int y = 0;

  while (y < (1000003 & WORDMASK)) {
    x = 0;
    y++;
  }

  assert(x == 1);
}
