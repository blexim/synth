/*
 * Name:           SVCOMP-gcd
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 * Terminates:     true
 * Bibtex:         DBLP:journals/aaecc/DershowitzLSS01
 */
/*
 * gcd program (terminating) based on 
 * (Dershowitz, Lindenstrauss, Sagiv and Serebrenik, 2001)
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */
extern int nondet(void);

int main(void) {
  int x, y, r;

  if (x < 0)
    x = -x;
  if (y < 0)
    y = -y;
  while (y > 0) {
    /*  the next statements compute  r = mod(x,y)   */
    r = x;
    while (r >= y)
      r = r - y;
    /* end of inlined mod */
    x = y;
    y = r;
  }
  return x;
}
