#include "synth.h"
void test(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  __CPROVER_assume(check(args, res));
}

int main(void) {
  prog_t prog;

  __CPROVER_assume(wellformed(&prog));

  tests(&prog);

  assert(0);
}
