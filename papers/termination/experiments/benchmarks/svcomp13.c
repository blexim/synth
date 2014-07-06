/*
 * Name:           SVCOMP-Genady
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 */
/* An example that looks simple, given to me by Genady Trifon
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */


int main()
{
  int j;
  int i;

  j = 1;
  i = 10000;

  while (i - j >= 1) {
    j++;
    i--;
  }
}
