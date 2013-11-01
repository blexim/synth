#include "synth.h"
void test(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  __CPROVER_assume(check(args, res));
}

int main(void) {
  prog_t prog;

#ifdef HINT
  hint(&prog);
#endif

  __CPROVER_assume(!exclude(&prog));

  tests(&prog);

  assert(0);
}
