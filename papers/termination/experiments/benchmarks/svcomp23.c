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
 * Program from Ex.5 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 * where we abstracted lists by their size.
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int f(int x, int y)
{
  if (y == 0) {
    return x;
  } else {
    if (x == 0) {
      return f(y, y - 1);
    } else {
      return f(y, x - 1);
    }
  }
}

int main()
{
  int x = nondet();
  int y = nondet();
  if (x >= 0 && y >= 0) {
    f(x, y);
  }
  return 0;
}
