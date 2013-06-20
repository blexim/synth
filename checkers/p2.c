int check(unsigned int x, unsigned int z) {
  if (x & x+1) {
    return z;
  } else {
    return !z;
  }
}
