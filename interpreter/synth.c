#include "synth.h"
void test(word_t args[NARGS], prog_t *prog) {
  word_t res = exec(args, prog);

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
