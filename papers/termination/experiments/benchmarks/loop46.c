/*
 * Name:           loop44
 * Linear-program: true
 * Linear-rank:    false
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  ?
 * Source:         Ramsey vs. Lexicographic Termination Proving, TACAS'13
 * Bibtex:         DBLP:conf/tacas/CookSZ13
 * Ranking function: m - x
 * Terminates:     true
 */

int main(void) {
  unsigned int x, m;

  while (x != m) {
    if (x > m)
      x = 0;
    else
      x++;
  }
}
