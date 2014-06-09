/*
 * Name:           SVCOMP-BradleyMannaSipma-2005ICALP
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    true
 * Float:          false
 * Bitvector:      unk
 * Lexicographic:  unk
 */

int main(void)
{
  int x, y, N;

  x = nondet();
  y = nondet();
  N = nondet();

  if (N >= 536870912 || x >= 536870912 || y >= 536870912 || x < -1073741824) {
    return 0;
  }

  if (x + y >= 0) {
    while (x <= N) {
      if (nondet()) {
        x = 2 * x + y;
        y = y + 1;
      } else {
        x = x + 1;
      }
    }
  }
}
