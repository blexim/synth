#include "synth.h"

#include <math.h>

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  float f = *((float *) &x);
  float g = *((float *) &z);

  if (!isnormal(f)) {
    return 1;
  }

  //if (!isnormal(g)) {
  //  return 0;
  //}

  if (f > 1e6) {
    return 1;
  }

  return g == 2*f;
}
