#include "synth.h"

#include <math.h>

union uf {
  word_t w;
  fword_t f;
};

int check(word_t args[NARGS], word_t z) {
  union uf uf;

  word_t x = args[0];

  uf.w = x;
  fword_t f = uf.f;
  fword_t r = 2*f;

  uf.w = z;
  fword_t g = uf.f;

  if (!isnormal(f) || !isnormal(r)) {
    return 1;
  }

  if (!isnormal(g)) {
    return 0;
  }

  return g == 2*f;
}
