/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/sas/Urban13
 * Tweaked:        true
 */
/*
 * Program from Fig.1 of
 * 2013WST - Urban - Piecewise-Defined Ranking Functions
 *
 * Date: 12.12.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int main()
{
  int x1, x2;
  while (x1 <= 10) {
    x2 = 10;
    while (x2 > 1) {
      x2 = x2 - 1;
    }
    x1 = x1 + 1;
  }
}
