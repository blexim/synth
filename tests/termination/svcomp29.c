/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/vmcai/P04
 */
/*
 * Program from Example 2 of
 * 2004VMCAI - Podelski,Rybalchenko - A complete method for the synthesis of linear ranking functions
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int main()
{
  int x;
  while (x >= 0) {
    x = -2 * x + 10;
  }
  return 0;
}
