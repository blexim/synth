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
/*
 * Terminating Program 
 *
 * Date: 18.12.2013
 * Author: urban@di.ens.fr
 */

extern int nondet(void);

int main()
{
  int x, y;
  while (x != 0 && y > 0) {
    if (x > 0) {
      if (nondet()) {
        x = x - 1;
        y = nondet();
      } else {
        y = y - 1;
      }
    } else {
      if (nondet()) {
        x = x + 1;
      } else {
        y = y - 1;
        x = nondet();
      }
    }
  }
}
