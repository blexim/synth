#include "synth.h"

extern prog_t prog;

unsigned int main(void) {
  word_t cex_args[NARGS];
  word_t res = exec(cex_args, prog);

  assert(check(cex_args, res));
}
