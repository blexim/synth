/*
 * Name:           SVCOMP-HarrisLalNoriRajamani-SAS2010
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */
/*
 * Program from Fig.1 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);


void f(int d)
{
  int x, y, k, z = 1;
  if (k > 1073741823) {
    return;
  }
  // ...
L1:
  while (z < k) {
    z = 2 * z;
  }
L2:
  while (x > 0 && y > 0) {
    // ...
    if (nondet()) {
    P1:
      x = x - d;
      y = nondet();
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}

int main()
{
  if (nondet()) {
    f(1);
  } else {
    f(2);
  }
}
