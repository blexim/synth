#include "synth.h"

#include <math.h>

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  float f = *((float *) &x);
  float g = *((float *) &z);

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
