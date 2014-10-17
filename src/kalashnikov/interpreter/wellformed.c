#include "synth.h"
#include "exec.h"

#define ISCONST(x) (x < CONSTS + 2)

int wellformed(prog_t *prog) {
  int i, j;

  for (i = 0; i < LEN(prog); i++) {
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
    if (p1 >= i + NARGS + CONSTS + 2) {
      return 0;
    }

    if (p2 >= i + NARGS + CONSTS + 2) {
      return 0;
    }

    if (p3 >= i + NARGS + CONSTS + 2) {
      return 0;
    }
  }

  // Constants must be ordered & no duplicates.
  if (CONSTS > 0 && prog->consts[0] <= 1) {
    return 0;
  }

  for (i = 0; i < CONSTS-1; i++) {
    if (prog->consts[i] >= prog->consts[i+1]) {
      return 0;
    }
  }

  return 1;
}
