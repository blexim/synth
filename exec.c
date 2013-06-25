#include "synth.h"

#define PLUS 0
#define MINUS 1
#define MUL 2
#define DIV 3
#define NEG 4
#define AND 5
#define OR 6
#define XOR 7
#define NOT 8
#define SHL 9
#define LSHR 10
#define ASHR 11
#define LE 12
#define LT 13
#define GE 14
#define GT 15

#define ARG 0
#define CONST 1

word_t parm(word_t A[], unsigned int i, prog_t prog) {
  if (prog.xparms[i] == 1) {
    return prog.parms[i];
  } else {
    word_t idx = prog.parms[i];
    return A[idx];
  }
}

word_t exec(word_t args[NARGS], prog_t prog) {
  word_t A[SZ+NARGS];
  op_t op;
  word_t p1, p2, res;
  unsigned int i;

  for (i = 0; i < NARGS; i++) {
    A[i] = args[i];
  }

  for (i = 0; i < SZ; i++) {
    op = prog.ops[i];
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

  return A[SZ+NARGS-1];
}
