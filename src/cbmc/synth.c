#include "synth.h"
void test(prog_t *prog, word_t args[NARGS]) {
  __CPROVER_assume(check(prog, args));
}

int main(void) {
  prog_t prog;

#ifdef HINT
  hint(&prog);
#endif

  __CPROVER_assume(wellformed(&prog));
  __CPROVER_assume(!exclude(&prog));

  tests(&prog);

  assert(0);
}
