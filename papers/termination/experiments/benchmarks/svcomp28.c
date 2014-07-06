/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/sigsoft/Nori013
 */
/*
 * Program from Fig.8 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int main()
{
  int u, x, v, y, w, z, c;
  u = x;
  v = y;
  w = z;
  c = 0;
  while (x >= y) {
    c = c + 1;
    if (z > 1) {
      z = z - 1;
      x = x + z;
    } else {
      y = y + 1;
    }
  }
}
