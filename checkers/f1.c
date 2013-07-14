#include "synth.h"
#include <math.h>

#define ERRLIM 1.0

int check(word_t args[NARGS], word_t z) {
  float *xp = (float *) &args[0];
  float x = (float) args[0];

  float *yp = (float *) &z;
  float y = (float) z;

  if (!isnormal(x)) {
    return 1;
  }

  if (x <= 1.0) {
    return 1;
  }

  if (x >= 1e6) {
    return 1;
  }

  float v = x*(1.5f - (x * 0.5f * y*y));
  //float v = y;
  float w = v*v;
  float q = 1.0 / w;

  if (q <= 0.0) {
    return 0;
  }

  float abserr;

  if (x > q) {
    abserr = x - q;
  } else {
    abserr = q - x;
  }

  float relerr = abserr / x;

  if (relerr < ERRLIM) {
    return 1;
  } else {
    return 0;
  }
}
