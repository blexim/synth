#include "synth.h"
#include "exec.h"

int exclude_1(unsigned int idx, op_t op, word_t p1, word_t p2, bit_t x1, bit_t x2) {
  // Exclude anything with an invalid opcode...
  if (op > MAXOPCODE) {
    return 1;
  }

  // Exclude anything referring to an unitialised register...
  if (x1 == ARG && p1 >= (idx + NARGS)) {
    return 1;
  }

  if (x2 == ARG && p2 >= (idx + NARGS)) {
    return 1;
  }

  // Exclude anything with 2 const operands...
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

  // Symmetry break: only add/sub positive values.
  if ((op == PLUS || op == MINUS) &&
      x2 == CONST) {
    return p2 & (1 << (WIDTH-1));
  }

  return 0;
}

int exclude_2(unsigned int idx,
    op_t op1, bit_t x11, word_t p11, bit_t x12, word_t p12,
    op_t op2, bit_t x21, word_t p21, bit_t x22, word_t p22) {
  // Exclude sequences like:
  //
  // t1 = OP1 R C
  // t2 = OP1 t1 C
  if (x21 == ARG && p21 == (idx + NARGS) &&
      x12 == CONST && x22 == CONST &&
      op1 == op2) {
    return 1;
  }
}

void exclude(prog_t *prog) {
  unsigned int i;

  for (i = 0; i < SZ; i++) {
    
    __CPROVER_assume(!exclude_1(i,
          prog->ops[i],
          prog->parms[i*2], prog->parms[i*2+1],
          prog->xparms[i*2], prog->xparms[i*2+1]));
  }

  for (i = 0; i < SZ-1; i++) {
    op_t op1, op2;
    bit_t x11, x12, x21, x22;
    word_t p11, p12, p21, p22;

    op1 = prog->ops[i];
    op2 = prog->ops[i+1];

    x11 = prog->xparms[i*2];
    x12 = prog->xparms[i*2+1];
    x21 = prog->xparms[i*2+2];
    x22 = prog->xparms[i*2+3];

    p11 = prog->parms[i*2];
    p12 = prog->parms[i*2+1];
    p21 = prog->parms[i*2+2];
    p22 = prog->parms[i*2+3];

    __CPROVER_assume(!exclude_2(i,
          op1, x11, p11, x12, p12, op2, x21, p21, x22, p22));
  }
}
