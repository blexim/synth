/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/popl/LeeJB01
 */
/*
 * Program from Ex.1 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 * where we abstracted lists by their size.
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int r1(int ls, int a)
{
  if (ls == 0) {
    return a;
  } else {
    return r1(ls - 1, ls + 1 + a);
  }
}

int rev(int ls)
{
  return r1(ls, 0);
}

int main()
{
  int ls = nondet();
  if (ls >= 0) {
    rev(ls);
  }
  return 0;
}
