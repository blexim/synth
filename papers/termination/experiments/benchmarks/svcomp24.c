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
 * Program from Ex.6 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 * where we abstracted lists by their size.
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int f(int a, int b);

int g(int c, int d);

int f(int a, int b)
{
  if (b == 0) {
    return g(a, 0);
  } else {
    return f(1 + a, b - 1);
  }
}

int g(int c, int d)
{
  if (c == 0) {
    return d;
  } else {
    return g(c - 1, 1 + d);
  }
}

int main()
{
  int a = nondet();
  int b = nondet();
  if (a >= 0 && b >= 0) {
    f(a, b);
  }
  return 0;
}
