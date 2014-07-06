/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    true
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 */
//#Termination
/*
 * Date: November 2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 
 */

extern int nondet(void);

int main()
{
  int x, y, z;
  //int m, n;

  if (nondet()) {
    x = 1;
  } else {
    x = -1;
  }
  while (y < 2 && z < 2) {
    y = y + x;
    z = z - x;
  }
  return 0;
}
