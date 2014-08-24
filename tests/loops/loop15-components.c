#include "synth.h"

void prefix(word_t vars[1]) {
}

int guard(word_t vars[1]) {
  return vars[1] > 0;
}

int body(word_t vars[1]) {
  vars[0] = (vars[0] - 1) & vars[0];

  return 1;
}

int assertion(word_t vars[2]) {
  return 1;
}
