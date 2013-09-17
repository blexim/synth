#include "synth.h"
#include <math.h>

typedef union {
  word_t i;
  fword_t f;
} fi_t;

int check(word_t args[2], word_t res[2]) {
  fi_t fi;

  fi.i = args[0];
  fword_t a = fi.f;

  fi.i = args[1];
  fword_t b = fi.f;

  if (!isnormal(a) || !isnormal(b)) {
    return 1;
  }

  fword_t absa = (a < 0 ? -a : a);
  fword_t absb = (b < 0 ? -b : b);

  if (absa < absb) {
    return 1;
  }

  fword_t s = a + b;
  fword_t b2 = s - a;
  fword_t a2 = s - b2;
  fword_t db = b - b2;
  fword_t da = a - a2;
  fword_t t = da + db;

  fi.i = res[0];
  fword_t rs = fi.f;

  fi.i = res[1];
  fword_t rt = fi.f;

  if (s == rs && t == rt) {
    return 1;
  }

  return 0;
}
