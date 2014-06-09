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
 * Program from Ex.3 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int a(int m, int n)
{
  if (m <= 0) {
    return n + 1;
  } else {
    if (n <= 0) {
      return a(m - 1, 1);
    } else {
      return a(m - 1, a(m, n - 1));
    }
  }
}

int main()
{
  int m = nondet();
  int n = nondet();
  if (m >= 0 && n >= 0) {
    a(m, n);
  }
  return 0;
}
