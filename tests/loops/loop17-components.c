#include "synth.h"

void prefix(word_t vars[1]) {
  vars[0] = 1;
}

int guard(word_t vars[1]) {
  return vars[0] > 0;
}

int body(word_t vars[1]) {
  word_t x = vars[0];

  x = -x / 2;

  vars[0] = x;

  return 1;
}

int assertion(word_t vars[1]) {
  return 1;
}
