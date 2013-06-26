#include "synth.h"

void test(word_t args[NARGS], prog_t prog) {
  word_t res = exec(args, prog);

  __CPROVER_assume(check(args, res));
}

#define isop(i, op) (ops[i] == op)
#define isconst(i, c) (parms[i] == c && xparms[i] == 1)

int main(void) {
  word_t parms[SZ*2];
  bit_t xparms[SZ*2];
  op_t ops[SZ];
  int xors = 0;
  int shrs = 0;
  int ands = 0;
  int muls = 0;

  prog_t prog;

  prog.ops = ops;
  prog.parms = parms;
  prog.xparms = xparms;

  for (int i = 0; i < SZ; i++) {
    __CPROVER_assume(ops[i] <= MAXOPCODE);

    if (ops[i] == 10) {
      shrs++;
    } else if (ops[i] == 7) {
      xors++;
    } else if (ops[i] == 5) {
      ands++;
    } else if (ops[i] == 2) {
      muls++;
    }

    __CPROVER_assume((xparms[i*2] == 0) && (parms[i*2] < (i+NARGS)));
    __CPROVER_assume(xparms[i*2+1] || (parms[i*2+1] < (i+NARGS)));
  }

#ifdef HINT
  hint(prog);
#endif

  tests(prog);

  assert(0);
}
