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
 * Program from Fig.3 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int x;

void foo(void)
{
  x--;
}


int main()
{
  x = nondet();

  while (x > 0) {
    if (nondet()) {
      x--;
    } else {
      x--;
    }
  }
  return 0;
}
