#include "synth.h"

void prefix(word_t args[1]) {
  args[0] = 100;
}

int guard(word_t args[1]) {
  sword_t x = args[0];

  //return x <= 100 && x >= -100 && x != 0;
  return x != 0;
}

int body(word_t args[1]) {
  sword_t x = args[0];

  if (x < 0) {
    x = -x - 1;
  } else {
    x = -x + 1;
  }

  args[0] = x;

  return 1;
}

int assertion(word_t args[1]) {
  return 1;
}
