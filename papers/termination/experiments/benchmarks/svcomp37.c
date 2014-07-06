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
 * Terminating program that has no linear lexicographic ranking function.
 * The program chooses nondeterministically the variable x or y and assigns to
 * it the result of   minimum(x,y)-1
 * The term   minimum(x,y)  is a ranking function for this program.
 *
 * Amir Ben-Amram (TelAviv) showed me this program when we met in Perpignan at
 * SAS 2010.
 *
 * Date: 1.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */


extern int nondet(void);

int main()
{
  int x, y;
  while (x > 0 && y > 0) {
    if (nondet()) {
      if (x < y) {
        y = x - 1;
      } else {
        y = y - 1;
      }
      x = nondet();
    } else {
      if (x < y) {
        x = x - 1;
      } else {
        x = y - 1;
      }
      y = nondet();
    }
  }
}
