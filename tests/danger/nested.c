int Gi(unsigned int i, unsigned int j, unsigned int ip, unsigned int jp) {
  return i <= 10;
}

int Go(unsigned int i, unsigned int j) {
  return j <= i;
}

int A(unsigned int i, unsigned int j) {
  return j != 12;
}

// Solution:

int Do(unsigned int i, unsigned int j) {
  return j <= 12 && i == 11;
}

int Ro(unsigned int i, unsigned int j) {
  return i - j + 1;
}

int Co(unsigned int i, unsigned int j, unsigned int ip, unsigned int jp) {
  return jp == j - 1 && ip == 11 && i == 0 && jp <= ip;
}

int Di(unsigned int i, unsigned int j, unsigned int ip, unsigned int jp) {
  return jp == j  - 1 && i <= 11 && ip == 11 && jp <= ip;
}

int Ri(unsigned int i, unsigned int j, unsigned int ip, unsigned int jp) {
  return 12 - i;
}

unsigned int main(void) {
  unsigned int i, j, ip, jp;
  unsigned int i0 = 11, j0 = 0;

  // Initiation for outer loop
  assert(!(Do(i, j) && !Go(i, j)) || !A(i, j));
  // Outer ranking function bounded
  assert(!(Do(i, j) && Go(i, j)) || Ro(i, j) > 0);

  // Outer intermediate predicate holds when outer loop is taken
  assert(!(Do(i, j) && Go(i, j)) || Co(0, j + 1, i, j));

  // Inner initiation
  assert(!(Co(i, j, ip, jp)) || Di(i, j, ip, jp));
  // Inner danger invariant re-establishes outer danger invariant after the inner loop (i.e.
  // outer danger invariant is inductive) and...
  assert(!(Di(i, j, ip, jp) && !Gi(i, j, ip, jp)) || (Do(i, j)));
  // Inner danger invariant establishes that outer ranking function decreases
  assert(!(Di(i, j, ip, jp) && !Gi(i, j, ip, jp)) || (Ro(i, j) < Ro(ip, jp)));

  // Inner ranking function is bounded
  assert(!(Di(i, j, ip, jp) && Gi(i, j, ip, jp)) || Ri(i, j, ip, jp) > 0); 
  // Inner danger invariant is inductive
  assert(!(Di(i, j, ip, jp) && Gi(i, j, ip, jp)) || Di(i + 1, j, ip, jp));
  // Inner ranking function decreases
  assert(!(Di(i, j, ip, jp) && Gi(i, j, ip, jp)) || Ri(i + 1, j, ip, jp) < Ri(i, j, ip, jp));
}
