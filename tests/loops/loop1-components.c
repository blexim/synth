#include "synth.h"

void prefix(word_t vars[2]) {
  vars[0] = 1;
}

int guard(word_t vars[2]) {
  return vars[1] > 0;
}

void body(word_t vars[2]) {
  vars[0] += 2;
  vars[1] -= 1;
}

int assertion(word_t vars[2]) {
  return vars[0] % 2;
}
