#include "synth.h"
#include <math.h>

#define ERRLIM 0.1

union ia {
  word_t i;
  float f;
};

int check(word_t args[NARGS], word_t z) {
  union ia ia;

  ia.i = args[0];
  float x = ia.f;

  ia.i = z;
  float y = ia.f;

  if (!isnormal(x)) {
    return 1;
  }

  if (x <= 0.1) {
    return 1;
  }

  if (x >= 100.0) {
    return 1;
  }

  if (y <= 0.0) {
    return 0;
  }

  float v = y*(1.5f - (x * 0.5f * y*y));
  float res = v*v*x;

  if ((res >= 1.0 - ERRLIM) && (res <= 1.0 + ERRLIM)) {
    return 1;
  } else {
    return 0;
  }
}
