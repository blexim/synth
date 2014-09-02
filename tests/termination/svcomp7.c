/*
 * Name:           BrockschmidtCookFuhs-CAV13-2
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    true
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/cav/BrockschmidtCF13
 */

/*
 * Program from the introduction of
 * 2013CAV - Brockschmidt,Cook,Fuhs - Better termination proving through cooperation -draft
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int main()
{
  int x, y;
  y = 1;

  while (x > 0) {
    x = x - y;
    y = y + 1;
  }
}
