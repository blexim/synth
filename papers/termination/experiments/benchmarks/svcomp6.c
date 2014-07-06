/*
 * Name:           SVCOMP-BrockschmidtCookFuhs-2013CAV-1
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:conf/cav/BrockschmidtCF13
 */

int main()
{
  int i, j, n;

  while (i < n) {
    j = 0;
    while (j <= i) {
      j = j + 1;
    }
    i = i + 1;
  }
}
