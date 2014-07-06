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
 * Damien Massé showed me this program
 *
 * Date: 18.12.2013
 * Author: urban@di.ens.fr
 */

extern int nondet(void);

int main()
{
  int x;
  while (x <= 1000) {
    if (nondet()) {
      x = -2 * x + 2;
    } else {
      x = -3 * x - 2;
    }
  }
}
