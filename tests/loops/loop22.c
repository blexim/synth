int main(void) {
  unsigned char i;
  unsigned char c;

  i = 0;

  if (c == 0 || c > 255) {
    return 0;
  } else {
    c--;
  }

  while (c > 0) {
    i = i + 1;
    c = c >> 1;
  }

  assert(i < 7);

  return 0;
}
