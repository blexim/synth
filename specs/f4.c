#include "synth.h"
#include <math.h>

/*
 * Calculate square root.
 */

#define ERRLIM 0.9

union uf {
  word_t x;
  fword_t f;
};

int check(word_t args[NARGS], word_t res) {
  union uf u;

  u.x = args[0];
  fword_t x = u.x;

  if (!isnormal(x) || x < 1.0 || x > 1e6) {
    return 1;
  }

  u.x = res;
  fword_t z = u.f;

  fword_t s = z*z;

  fword_t err;

  if (s > x) {
    err = s - x;
  } else {
    err = x - s;
  }

  err /= x;

  if (err <= ERRLIM) {
    return 1;
  }

  return 0;
}
