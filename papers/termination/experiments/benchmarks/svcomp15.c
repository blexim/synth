/*
 * Name:           SVCOMP-HarrisLalNoriRajamani-SAS2010
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
 * Program from Fig.1 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);


int main()
{
  int d, x, y, k ,z;

  z = 1;

  if (nondet()) {
    d = 1;
  } else {
    d = 2;
  }

  if (k >= 128) {
    return;
  }

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
