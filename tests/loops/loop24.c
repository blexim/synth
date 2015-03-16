/*
 * Danger invariant:
 * 
 * a_0 = 0
 * i_0 = anything
 * c_0 = anything
 *
 * D(i, c, a) = a == 0
 * R(i, c, a) = -i
 */

int main(void) {
  unsigned int i, c, a;

  i = 0;
  c = 0;

  while (i < 1000) {
    c = c+i;
    i++;
    
  }

  assert(a > 0);
}

