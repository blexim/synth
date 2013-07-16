#include "synth.h"
#include "exec.h"

#define ISCONST(x) (x < CONSTS)

int exclude_1(unsigned int idx, op_t op, param_t p1, param_t p2,
    word_t consts[CONSTS]) {
  // Exclude anything with an invalid opcode...
  __CPROVER_assume(op <= MAXOPCODE);

  // Exclude anything referring to an unitialised register...
  __CPROVER_assume(p1 < (idx + NARGS + CONSTS));

  __CPROVER_assume(p2 < (idx + NARGS + CONSTS));

  // Exclude any binary op with 2 const operands...
  if ((op != NEG) && (op != NOT)) {
    __CPROVER_assume(!ISCONST(p1) || !ISCONST(p2));
  } else {
    // Exclude any unary ops with a const operand...
    __CPROVER_assume(!ISCONST(p1));

    // Break symmetry: force 2nd (unused) arg to be #0
    __CPROVER_assume(p2 == 0);
  }

  // Break symmetry: for any commutative op, put the smaller operand first.
  // This also means that if an instruction has a const operand, it's the first
  // one.
  if (op == PLUS ||
      op == MUL ||
      op == AND ||
      op == OR ||
      op == XOR) {
    __CPROVER_assume(p1 <= p2);
  }

  // Exclude nops.
  if ((op == PLUS || op == MINUS || op == OR || op == XOR ||
        op == SHL || op == LSHR || op == ASHR) && ISCONST(p1)) {
    __CPROVER_assume(consts[p1] != 0);
  }

  // More nops. 
  if ((op == MUL || op == DIV) && ISCONST(p1)) {
    __CPROVER_assume(consts[p1] != 1);

    // While we're here, let's not multiply or divide by 0 either.
    __CPROVER_assume(consts[p1] != 0);
  }

  // More nops.
  if (op == AND && ISCONST(p1)) {
    __CPROVER_assume(consts[p1] != (word_t) -1);
  }

  // More nops.
  if (op == AND || op == OR) {
    __CPROVER_assume(p1 != p2);
  }

  // Symmetry break: only add/sub positive values.
  if (op == PLUS && ISCONST(p1)) {
    sword_t c = consts[p1];
    __CPROVER_assume(c > 0);
  }

  if (op == MINUS && ISCONST(p2)) {
    sword_t c = consts[p2];
    __CPROVER_assume(c > 0);
  }

  // Symmetry break: disallow x * -1, x / -1 (use unary neg instead)
  if ((op == MUL || op == DIV) && ISCONST(p1)) {
    __CPROVER_assume(consts[p1] != (word_t) -1);
  }
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
    param_t p1, p2;

    op = prog->ops[i];
    p1 = prog->params[i*2];
    p2 = prog->params[i*2+1];
    
    exclude_1(i, op, p1, p2, prog->consts);
  }

#if 0
  for (i = 0; i < SZ-1; i++) {
    op_t op1, op2;
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
#endif
}
