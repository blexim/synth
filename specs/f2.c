#include "synth.h"

#include <math.h>

union uf {
  word_t w;
  fword_t f;
};

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  union uf uf;

  uf.w = x;
  fword_t f = uf.f;

  uf.w = z;
  fword_t g = uf.f;

  if (!isnormal(f)) {
    return 1;
  }

  if (!isnormal(g)) {
    return 0;
  }

  if (f < 0 || f > 1e10) {
    return 1;
  }

  return g >= f;
}
