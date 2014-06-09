/*
 * Name:           SVCOMP-Genady
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */
/* An example that looks simple, given to me by Genady Trifon
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */


int main()
{
  int j = 1;
  for (int i = 10000; i - j >= 1; i--) {
    j++;
  }
}
