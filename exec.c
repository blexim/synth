#include "synth.h"
#include "exec.h"

word_t parm(word_t A[], unsigned int i, prog_t *prog) {
  if (prog->xparms[i] == 1) {
    return prog->parms[i];
  } else {
    word_t idx = prog->parms[i];
    return A[idx];
  }
}

word_t exec(word_t args[NARGS], prog_t *prog) {
  word_t A[SZ+NARGS];
  op_t op;
  word_t p1, p2, res, result;
  unsigned int i;

  for (i = 0; i < NARGS; i++) {
    A[i] = args[i];
  }

  for (i = 0; i < SZ; i++) {
    op = prog->ops[i];
    p1 = parm(A, 2*i, prog);
    p2 = parm(A, 2*i + 1, prog);

    switch(op) {
    case PLUS:
      res = p1 + p2;
      break;
    case MINUS:
      res = p1 - p2;
      break;
    case MUL:
      res = p1 * p2;
      break;
    case DIV:
#ifdef SYNTH
      __CPROVER_assume(p2 != 0);
#else
      assert(p2 != 0);
#endif
      res = p1 / p2;
      break;
    case NEG:
      res = -p1;
      break;
    case AND:
      res = p1 & p2;
      break;
    case OR:
      res = p1 | p2;
      break;
    case XOR:
      res = p1 ^ p2;
      break;
    case NOT:
      res = ~p1;
      break;
    case SHL:
      res = p1 << p2;
      break;
    case LSHR:
      res = p1 >> p2;
      break;
    case ASHR:
      sword_t i1 = p1;
      sword_t i2 = p2;

      res = (word_t) (i1 >> i2);
      break;
    case LE:
      if (p1 <= p2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    case LT:
      if (p1 < p2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    case GE:
      if (p1 >= p2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    case GT:
      if (p1 > p2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    default:
      __CPROVER_assume(0);
      break;
    }

    A[i+NARGS] = res;
  }

  result = A[SZ+NARGS-1];

  return result;
}
