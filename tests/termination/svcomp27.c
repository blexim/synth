/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     false
 * Bibtex:         DBLP:conf/sigsoft/Nori013
 */
/*
 * Program from Fig.7 of
 * 2013FSE - Nori,Sharma - Termination Proofs from Tests
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int nondet(void);

int main()
{
  int a, i, b, j, c, M, N;
  a = i;
  b = j;
  c = 0;
  while (i < M || j < N) {
    i = i + 1;
    j = j + 1;
    c = c + 1;
  }
}
