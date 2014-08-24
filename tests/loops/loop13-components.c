#include "synth.h"

void prefix(word_t args[1]) {
  fi_t fi;

  fi.f = 100.0;
  args[0] = fi.x;
}

int guard(word_t args[1]) {
  fi_t fi;

  fi.x = args[0];
  return fi.f > 0.0;
}

int body(word_t args[1]) {
  fi_t fi;

  fi.x = args[0];
  fi.f /= 2;
  args[0] = fi.x;

  return 1;
}

int assertion(word_t args[1]) {
  return 1;
}
