/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */
/*
 * Program from Ex.4 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int p(int m, int n, int r)
{
  if (r > 0) {
    return p(m, r - 1, n);
  } else {
    if (n > 0) {
      return p(r, n - 1, m);
    } else {
      return m;
    }
  }
}

int main()
{
  int m = nondet();
  int n = nondet();
  int r = nondet();
  if (m >= 0 && n >= 0 && r >= 0) {
    p(m, n, r);
  }
  return 0;
}
