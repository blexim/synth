#include "synth.h"

void prefix(word_t vars[1]) {
  vars[0] = 1;
}

int guard(word_t vars[1]) {
  return vars[0] > 0;
}

void body(word_t vars[1]) {
  vars[0] += 1;
}

int assertion(word_t vars[1]) {
  return 1;
}
