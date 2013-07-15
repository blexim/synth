#include "synth.h"
#include "exec.h"

int exclude_1(unsigned int idx, op_t op, bit_t x1, word_t p1, bit_t x2, word_t p2) {
  // Exclude anything with an invalid opcode...
  __CPROVER_assume(op <= MAXOPCODE);

  // Exclude anything referring to an unitialised register...
  __CPROVER_assume(!(x1 == ARG && p1 >= (idx + NARGS)));

  __CPROVER_assume(!(x2 == ARG && p2 >= (idx + NARGS)));

  // Exclude anything with 2 const operands...
  __CPROVER_assume(!(x1 == CONST && x2 == CONST));

  // Exclude any unary ops with a const operand...
  __CPROVER_assume(!((op == NEG || op == NOT) && x1 == CONST));

  // Break symmetry: for any unary op, force 2nd (unused) arg to be const 0.
  __CPROVER_assume(!((op == NEG || op == NOT) && (x2 == CONST && p2 == 0)));

  // Break symmetry: for any commutative op with 1 reg and 1 const operand,
  // put the reg first.  If both operands are reg, put the smaller one first.
  __CPROVER_assume(!((op == PLUS ||
      op == MUL ||
      op == AND ||
      op == OR ||
      op == XOR ||
      op == LT ||
      op == LE ||
      op == GT ||
      op == GE) && 
    x1 == CONST && x2 == CONST));

  __CPROVER_assume(!((op == PLUS ||
      op == MUL ||
      op == AND ||
      op == OR ||
      op == XOR ||
      op == LT ||
      op == LE ||
      op == GT ||
      op == GE) && 
    x1 == ARG && x2 == ARG && p1 > p2));

  // Exclude nops.
  __CPROVER_assume(!((op == PLUS || op == MINUS || op == OR || op == XOR ||
        op == SHL || op == LSHR || op == ASHR) &&
      x2 == CONST && p2 == 0));

  // More nops. 
  __CPROVER_assume(!((op == MUL || op == DIV) && 
      x2 == CONST && p2 == 1)); 

  // More nops.
  __CPROVER_assume(!(op == AND && x2 == CONST && p2 == ((word_t) -1)));

  // More nops.
  __CPROVER_assume(!((op == AND || op == OR) &&
      x1 == ARG && x2 == ARG &&
      p1 == p2));

  // Symmetry break: only add/sub positive values.
  __CPROVER_assume(!((op == PLUS || op == MINUS) &&
      x2 == CONST && (p2 & (1 << (WIDTH - 1)))));

  // Symmetry break: disallow x * -1, x / -1 (use unary neg instead)
  __CPROVER_assume(!((op == MUL || op == DIV) &&
      x2 == CONST && (p2 + 1 == 0)));
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

  // Exclude sequences like:
  //
  // t1 = PLUS R C
  // t2 = MINUS t1 C
  if (x21 == ARG && p21 == (idx + NARGS) && 
      x12 == CONST && x22 == CONST) {
    if (op1 == PLUS || op1 == MINUS) {
      if (op2 == PLUS || op2 == MINUS) {
        return 1;
      }
    }
  }
}

void exclude(prog_t *prog) {
  unsigned int i, j;

  for (i = 0; i < SZ; i++) {
    op_t op;
    bit_t x1, x2;
    word_t p1, p2;

    op = prog->ops[i];
    x1 = prog->xparms[i*2];
    x2 = prog->xparms[i*2+1];
    p1 = prog->parms[i*2];
    p2 = prog->parms[i*2+1];
    
    exclude_1(i, op, x1, p1, x2, p2);
  }

  for (i = 0; i < SZ-1; i++) {
    op_t op1, op2;
    bit_t x11, x12, x21, x22;
    word_t p11, p12, p21, p22;

    op1 = prog->ops[i];
    x11 = prog->xparms[i*2];
    x12 = prog->xparms[i*2+1];
    p11 = prog->parms[i*2];
    p12 = prog->parms[i*2+1];

    for (j = i+1; j < SZ; j++) {
      op2 = prog->ops[i+1];

      x21 = prog->xparms[i*2+2];
      x22 = prog->xparms[i*2+3];

      p21 = prog->parms[i*2+2];
      p22 = prog->parms[i*2+3];

      if ((x21 == ARG && p21 == (i + NARGS)) ||
          (x22 == ARG && p22 == (i + NARGS))) {
        __CPROVER_assume(!exclude_2(i,
              op1, x11, p11, x12, p12, op2, x21, p21, x22, p22));
      }
    }
  }
}
