/*
 * Name:           loop45
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  ?
 * Source:         Ramsey vs. Lexicographic Termination Proving, TACAS'13
 */

extern int nondet();

int main(void) {
  int x, y, d;

  while (x > 0 && y > 0 && d > 0) {
    if (nondet()) {
      x = x-1;
      d = nondet();
    }
    else {
      x = nondet();
      y = y-1;
      d = d-1;
    }
  }
}
