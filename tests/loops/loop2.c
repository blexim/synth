int main(void) {
  int i, j, a, b, flag;

  a = 0;
  b = 0;
  j = 1;

  if (flag) i = 0;
  else      i = 1;

  while (nondet) {
    a++;
    b += (j - i);
    i += 2;

    if (i % 2 == 0) j += 2;
    else            j++;
  }

  if (flag) {
    assert(a == b);
  }
}
