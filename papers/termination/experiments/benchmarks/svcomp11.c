/*
 * Name:           SVCOMP-CookSeeZuleger-TACAS13-3
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
 * Program from Fig.7b of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 9.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main()
{
  int x, y, z;

  while (x > 0 && y > 0 && z > 0) {
    if (nondet()) {
      x = x - 1;
    } else if (nondet()) {
      y = y - 1;
      z = nondet();
    } else {
      z = z - 1;
      x = nondet();
    }
  }
}
