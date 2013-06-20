#include "synth.h"

void test(word_t x, prog_t prog) {
  __CPROVER_assume(check(x, exec(x, prog)));
}

int main(void) {
  word_t parms[SZ*2];
  bit_t xparms[SZ*2];
  op_t ops[SZ];

  prog_t prog;

  prog.ops = ops;
  prog.parms = parms;
  prog.xparms = xparms;

  for (int i = 0; i < SZ; i++) {
    __CPROVER_assume(ops[i] <= MAXOPCODE);

    __CPROVER_assume((xparms[i*2] == 0) && (parms[i*2] < (i+1)));
    //__CPROVER_assume(xparms[i*2] || (parms[i*2] < (i+1)));
    __CPROVER_assume(xparms[i*2+1] || (parms[i*2+1] < (i+1)));
  }

  tests(prog);

  assert(0);
}
