#include "synth.h"
void test(word_t args[NARGS], prog_t *prog) {
  word_t res = exec(args, prog);

  __CPROVER_assume(check(args, res));
}

int main(void) {
  prog_t prog;

  for (int i = 0; i < SZ; i++) {
    __CPROVER_assume(prog.ops[i] <= MAXOPCODE);
    __CPROVER_assume((prog.xparms[i*2] == 0) && (prog.parms[i*2] < (i+NARGS)));
    __CPROVER_assume(prog.xparms[i*2+1] || (prog.parms[i*2+1] < (i+NARGS)));
  }

#ifdef HINT
  hint(&prog);
#endif

#ifdef EXCLUDE
  exclude(&prog);
#endif

  tests(&prog);

  assert(0);
}
