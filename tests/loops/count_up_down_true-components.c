#include "synth.h"

void prefix(word_t vars[3]) {
  vars[0] = vars[2];
  vars[1] = 0;
}

int guard(word_t vars[3]) {
  return vars[0] > 0;
}

int body(word_t vars[3]) {
  vars[0]--;
  vars[1]++;
  return 1;
}

int assertion(word_t vars[3]) {
  return vars[1] == vars[2];
}
