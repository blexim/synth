/*
 * Name:           SVCOMP-aviad
 * Linear-program: false
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */

int main(void) {
  int a, tmp, count;

  a = nondet();
  count = 0;

  while (a > 1) {
    tmp = a % 2;

    if (tmp == 0) a = a / 2;
    else          a = a - 1;
    count++;
  }
}
