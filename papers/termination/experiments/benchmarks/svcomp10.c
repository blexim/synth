/*
 * Name:           SVCOMP-CookSeeZuleger-TACAS13-2
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/tacas/CookSZ13
 */
//#terminating
/*
 * Program from Fig.7a of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 9.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main()
{
  int x, y, d;

  while (x > 0 && y > 0 && d > 0) {
    if (nondet()) {
      x = x - 1;
      d = nondet();
    } else {
      x = nondet();
      y = y - 1;
      d = d - 1;
    }
  }
}
