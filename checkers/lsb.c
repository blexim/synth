int check(unsigned int x, unsigned int y, unsigned int z) {
  if (x == 0 && z == 0) {
    return 1;
  }

  for (unsigned int i = 0; i < 32; i++) {
    if (x & 1) {
      return z == 1;
    } else {
      if (z & 1) {
        return 0;
      } else {
        x >>= 1;
        z >>= 1;
      }
    }
  }
}
