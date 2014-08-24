#include "synth.h"

#include <math.h>

int prefix(word_t args[3]) {
  fi_t fi;

  fi.x = args[0];
  fword_t scaling = fi.f;

  fi.x = args[1];
  fword_t state = fi.f;

  fi.x = args[2];
  fword_t oldState = fi.f;

  return (0 < scaling) && (scaling < 1) &&
    oldState == 0 && state == 1;
}

int guard(word_t args[3]) {
  fi_t fi;

  fi.x = args[1];
  fword_t state = fi.f;

  fi.x = args[2];
  fword_t oldState = fi.f;

  return fabs(state - oldState) > 0.0;
}

int body(word_t vars[3]) {
  fi_t fi;

  fi.x = vars[0];
  fword_t scaling = fi.f;

  fi.x = vars[1];
  fword_t state = fi.f;

  fi.x = vars[2];
  fword_t oldState = fi.f;

  oldState = state;
  state *= scaling;

  fi.f = state;
  vars[1] = fi.x;

  fi.f = oldState;
  vars[2] = fi.x;

  return 1;
}
