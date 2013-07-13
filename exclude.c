#include "synth.h"
#include "exec.h"

int exclude_1(op_t op, word_t p1, word_t p2, bit_t x1, bit_t x2) {
  // First exclude anything with 2 const operands...
  if (x1 == CONST && x2 == CONST) {
    return 1;
  }

  // Exclude any unary ops with a const operand...
  if (op == NEG || op == NOT) {
    if (x1 == CONST) {
      return 1;
    }
  }

  // Break symmetry: for any commutative op with 1 reg and 1 const operand,
  // put the reg first.  If both operands are reg, put the smaller one first.
  if (op == PLUS ||
      op == MINUS ||
      op == MUL ||
      op == AND ||
      op == OR ||
      op == XOR) {
    if (x1 != x2) {
      // We have 1 reg and 1 const.  Exclude instructions that have a const first.
      return x1 == CONST;
    } else if (x1 == ARG && x2 == ARG) {
      // We have 2 reg.  Exclude anything where the 1st reg is the larger.
      return p1 > p2;
    }
  }

  // Exclude nops.
  if ((op == PLUS || op == MINUS || op == OR || op == XOR ||
        op == SHL || op == LSHR || op == ASHR) &&
      x2 == CONST && p2 == 0) {
    return 1;
  }

  // More nops.
  if ((op == MUL || op == DIV) && 
      x2 == CONST && p2 == 1) {
    return 1;
  }

  // More nops.
  if (op == AND && x2 == CONST && p2 == ((word_t) -1)) {
    return 1;
  }

  return 0;
}

void exclude(prog_t *prog) {
  for (unsigned int i = 0; i < SZ; i++) {
    __CPROVER_assume(!exclude_1(prog->ops[i],
          prog->parms[i*2], prog->parms[i*2+1],
          prog->xparms[i*2], prog->xparms[i*2+1]));
  }
}
