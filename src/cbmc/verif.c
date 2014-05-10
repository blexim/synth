#include "synth.h"

extern prog_t prog;

unsigned int main(void) {
  word_t cex_args[NARGS];

  assert(check(&prog, cex_args));
}
