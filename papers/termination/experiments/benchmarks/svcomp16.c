/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/sas/HarrisLNR10
 */
/*
 * Program from Fig.3 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

void foo(void)
{
  x--;
}


int main()
{
  int x;

  while (x > 0) {
    if (nondet()) {
      x--;
    } else {
      x--;
    }
  }
  return 0;
}
