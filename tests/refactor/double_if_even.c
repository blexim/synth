#include "synth.h"
#include "refactor.h"

void body(word_t x) {
  if (x % 2) {
    emit(x * 2);
  }
}
