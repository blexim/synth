#include "synth.h"

extern prog_t prog;

unsigned int main(void) {
  word_t cex_args[NARGS];
  word_t res[NRES];

  exec(&prog, cex_args, res);

  assert(check(cex_args, res));
}
