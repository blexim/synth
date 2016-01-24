int main(void) {
unsigned int i, j, k;

for (k = 0; k < 100; k++) {
  if (nondet()) j++;
}

__CPROVER_assume(i <= j && j <= 1000000);
i = nondet(); j = nondet();
__CPROVER_assume(i <= j && j <= 1000000 && i >= 1000000);

assert(i != j);
}
