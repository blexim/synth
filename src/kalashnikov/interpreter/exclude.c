#include "synth.h"
#include "exec.h"

#define ISCONST(x) (x < CONSTS)

int is_const(op_t op, param_t p1, param_t p2, param_t p3, word_t consts[CONSTS]) {
  word_t c1 = 0;
  word_t c2 = 0;
  sword_t s1 = 0;
  sword_t s2 = 0;

  if (ISCONST(p1)) {
    c1 = consts[p1];
    s1 = (sword_t) consts[p1];
  }

  if (ISCONST(p2)) {
    c2 = consts[p2];
    s2 = (sword_t) consts[p2];
  }

  // Exclude any binary op with 2 const operands...
  if ((op != NEG) && (op != NOT)) {
    if (ISCONST(p1) && ISCONST(p2)) {
      return 1;
    }
  } else {
    // Exclude any unary ops with a const operand...
    if (ISCONST(p1)) {
      return 1;
    }

    // Break symmetry: force 2nd (unused) arg to be #0
    if (p2 != (param_t) 0) {
      return 1;
    }
  }

  // Remove a couple of other const-returning instructions.
  if (op == MINUS || op == XOR || op == DIV) {
    if (p1 == p2) {
      return 1;
    }
  }

  if (op == MUL) {
    if ((ISCONST(p1) && c1 == 0) || (ISCONST(p2) && c2 == 0)) {
      return 1;
    }
  }

  if (op == ITE) {
    if (ISCONST(p1) && ISCONST(p2) && ISCONST(p3)) {
      return 1;
    }
  }

  return 0;
}

int is_nop(op_t op, param_t p1, param_t p2, param_t p3, word_t consts[CONSTS]) {
  word_t c = 0;
  sword_t s1 = 0;
  sword_t s2 = 0;

  if (ISCONST(p1)) {
    c = consts[p1];
    s1 = (sword_t) consts[p1];
  }

  if (ISCONST(p2)) {
    s2 = (sword_t) consts[p2];
  }

  if ((op == PLUS || op == MINUS || op == OR || op == XOR ||
        op == SHL || op == LSHR || op == ASHR) && ISCONST(p1)) {
    if (c == (word_t) 0) {
      return 1;
    }
  }

  if ((op == MUL || op == DIV) && ISCONST(p1)) {
    if (c == (word_t) 1) {
      return 1;
    }
  }

  if (op == AND && ISCONST(p1)) {
    if (c == (word_t) -1) {
      return 1;
    }
  }

  if (op == AND || op == OR) {
    if (p1 == p2) {
      return 1;
    }
  }

  return 0;
}

int is_symmetric(op_t op, param_t p1, param_t p2, param_t p3, word_t consts[CONSTS]) {
  word_t c1 = 0;
  word_t c2 = 0;
  sword_t s1 = 0;
  sword_t s2 = 0;

  if (ISCONST(p1)) {
    c1 = consts[p1];
    s1 = (sword_t) consts[p1];
  }

  if (ISCONST(p2)) {
    c2 = consts[p2];
    s2 = (sword_t) consts[p2];
  }

  // Break symmetry: for any commutative op, put the smaller operand first.
  // This also means that if an instruction has a const operand, it's the first
  // one.
  if (op == PLUS ||
      op == MUL ||
      op == AND ||
      op == OR ||
      op == XOR) {
    if (p1 > p2) {
      return 1;
    }
  }

  // Symmetry break: only add/sub positive values.
  if (op == PLUS) {
    if (ISCONST(p1) && s1 <= (word_t) 0) {
      return 1;
    }

    if (ISCONST(p2) && s2 <= (word_t) 0) {
      return 1;
    }
  }

  if (op == MINUS && ISCONST(p2)) {
    if (s2 <= (sword_t) 0) {
      return 1;
    }
  }

  // Symmetry break: disallow x * -1, x / -1 (use unary neg instead)
  if (op == MUL || op == DIV) {
    if (ISCONST(p1) && c1 == ((word_t) -1)) {
      return 1;
    }

    if (ISCONST(p2) && c2 == ((word_t) -1)) {
      return 1;
    }
  }

  if (op == ITE) {
    if (ISCONST(p1)) {
      return 1;
    }
  }

  return 0;
}

int exclude(prog_t *prog) {
  int i, j;

  for (i = 0; i < SZ; i++) {
    op_t op;
    param_t p1, p2, p3;

    op = prog->ops[i];
    p1 = prog->params[i*3];
    p2 = prog->params[i*3+1];
    p3 = prog->params[i*3+2];

#ifdef REMOVE_CONST
    if (is_const(op, p1, p2, p3, prog->consts)) {
      return 1;
    }
#endif

#ifdef REMOVE_NOPS
    if (is_nop(op, p1, p2, p3, prog->consts)) {
      return 1;
    }
#endif

#ifdef REMOVE_SYMMETRIC
    if (is_symmetric(op, p1, p2, p3, prog->consts)) {
      return 1;
    }
#endif
  }

  return 0;
}
