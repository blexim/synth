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
 * gcd program (terminating) based on 
 * (Dershowitz, Lindenstrauss, Sagiv and Serebrenik, 2001)
 *
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */
extern int nondet(void);

int gcd(int x, int y)
{
  int r;

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

int main()
{
  int x, y;

  x = nondet();
  y = nondet();

  gcd(x, y);
}
