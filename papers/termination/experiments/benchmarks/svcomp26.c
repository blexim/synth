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
 * Terminating program which has a r.f. based on minimum
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */

extern int nondet(void);

int main()
{
  int x, y;
  int z;

  x = nondet();
  y = nondet();

  while (y > 0 && x > 0) {
    if (x > y)
      z = y;
    else
      z = x;
    if (nondet()) {
      y = y + x;
      x = z - 1;
      z = y + z;
    } else {
      x = y + x;
      y = z - 1;
      z = x + z;
    }
  }
}
