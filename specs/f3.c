#include "synth.h"

#include <math.h>

int check(word_t args[NARGS], word_t z) {
  word_t x = args[0];

  float f = *((float *) &x);
  float g = *((float *) &z);

  if (!isnormal(f) || !isnormal(f*2)) {
    return 1;
  }

  //if (!isnormal(g)) {
  //  return 0;
  //}

  return g == 2*f;
}
