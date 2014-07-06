/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
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
  int x, y, z, m, n;
  if (nondet()) {
    x = 1;
  } else {
    x = -1;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  if (x > 0) {
    x++;
  } else {
    x--;
  }
  while (y < 100 && z < 100) {
    y = y + x;
    z = z - x;
  }
  return 0;
}
