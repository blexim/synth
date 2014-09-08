#include "synth.h"
#include "exec.h"

#define ISCONST(x) (x < CONSTS)

int wellformed(prog_t *prog) {
  int i, j;

#ifdef SEARCH
  for (i = 0; i < prog->len; i++) {
#else
  for (i = 0; i < SZ; i++) {
#endif
    op_t op;
    param_t p1, p2, p3;

    op = prog->ops[i];
    p1 = prog->params[i*3];
    p2 = prog->params[i*3+1];
    p3 = prog->params[i*3+2];

    // Must have a valid opcode.
    if (op > MAXOPCODE) {
      return 0;
    }

    // Operands must not refer to uninitialised registers.
    if (p1 >= i + NARGS + CONSTS) {
      return 0;
    }

    if (p2 >= i + NARGS + CONSTS) {
      return 0;
    }

    if (p3 >= i + NARGS + CONSTS) {
      return 0;
    }
  }

  // Constants must be ordered & no duplicates.
  for (i = 0; i < CONSTS-1; i++) {
    if (prog->consts[i] >= prog->consts[i+1]) {
      return 1;
    }
  }

  return 1;
}
