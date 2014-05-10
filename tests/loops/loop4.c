int main(void) {
  int i, j, N;

  assume(j < N);

  i = 0;

  while (i < j) {
    i++;
  }

  assert(i <= N);
}
