/*
 * Name:           CookSeeZuleger-TACAS13-1
 * Linear-program: true
 * Linear-rank:    unk
 * Conditional:    false
 * Float:          false
 * Bitvector:      unk
 * Lexicographic:  unk
 */
/*
 * Program from Fig.3 of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 8.6.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */


int main()
{
  int x, y;

  while (x > 0 && y > 0) {
    if (nondet()) {
      x = x - 1;
    } else {
      x = nondet();
      y = y - 1;
    }
  }
}
