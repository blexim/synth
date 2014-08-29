#include "synth.h"

extern solution_t solution;

unsigned int main(void) {
  word_t cex_args[NARGS];

  assert(check(&solution, cex_args) == MAXFIT);
}
