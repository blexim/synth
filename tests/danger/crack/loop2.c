int main(void) {
  unsigned int i, j;

  i = 0;
  __CPROVER_assume(inv(i, j));

  i = nondet();
  j = nondet();
  __CPROVER_assume(inv(i, j));
  __CPROVER_assume(i >= 1000000);

  assert(i != j);
}

int inv(unsigned int i, unsigned int j) {
  return i <= j && j <= 1000000;
}
