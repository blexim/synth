#include "synth.h"

extern prog_t prog;

unsigned int main(void) {
  word_t counterexample_x;
  word_t counterexample_z = exec(counterexample_x, prog);

  assert(check(counterexample_x, counterexample_z));
}
