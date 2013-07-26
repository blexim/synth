#include "synth.h"
#include "exec.h"

word_t exec(word_t args[NARGS], prog_t *prog) {
  op_t op;
  param_t a1, a2;
  word_t p1, p2, res, result;
  sword_t i1, i2;
  word_t A[SZ + NARGS + CONSTS];

  unsigned int i;

  for (i = 0; i < CONSTS; i++) {
    A[i] = prog->consts[i];
  }

  for (i = 0; i < NARGS; i++) {
    A[CONSTS + i] = args[i];
  }

  for (i = 0; i < SZ; i++) {
    op = prog->ops[i];
    a1 = prog->params[2*i];
    a2 = prog->params[2*i + 1];

    p1 = A[a1];
    p2 = A[a2];

    i1 = p1;
    i2 = p2;

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
#elif defined(SEARCH)
      if (p2 == 0) {
        break;
      }
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
    default:
#ifndef SEARCH
      __CPROVER_assume(0);
#endif
      break;
    }

    A[NARGS + CONSTS + i] = res;
  }

  result = A[NARGS + CONSTS + SZ - 1];

  return result;
}
