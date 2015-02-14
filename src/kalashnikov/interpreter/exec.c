#include "synth.h"
#include "exec.h"
#include "heaplib.h"

#include <math.h>

volatile int execok;


void exec(prog_t *prog, word_t args[NARGS], word_t results[NRES]) {
  op_t op;
  param_t a1, a2, a3;
  word_t p1, p2, p3, res;
  sword_t i1, i2, i3;
  word_t A[LEN(prog) + ARGBASE];

#ifdef FLOAT
  fword_t f1, f2;
  fi_t fi;
#endif

  unsigned int i;
  unsigned int j = 0;

  A[j++] = 0;
  A[j++] = 1;

  for (i = 0; i < CONSTS; i++) {
    A[j++] = prog->consts[i];
  }

  for (i = 0; i < NARGS; i++) {
    A[j++] = args[i];
  }

  for (i = 0; i < NRES; i++) {
    results[i] = 0;
  }

  for (i = 0; i < LEN(prog); i++) {
    if (i >= SZ) {
      break;
    }

    op = prog->ops[i];
    a1 = prog->params[3*i];
    a2 = prog->params[3*i + 1];
    a3 = prog->params[3*i + 2];

    p1 = A[a1];
    p2 = A[a2];
    p3 = A[a3];

#ifdef SEARCH
    p1 &= WORDMASK;
    p2 &= WORDMASK;
    p3 &= WORDMASK;
#endif

    i1 = p1;
    i2 = p2;
    i3 = p3;

#ifdef SEARCH
    // Sign extension
    SIGN_EXTEND(i1);
    SIGN_EXTEND(i2);
    SIGN_EXTEND(i3);
#endif

#ifdef FLOAT
    fi.x = p1;
    f1 = fi.f;

    fi.x = p2;
    f2 = fi.f;
#endif

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
      assume(p2 != 0);
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
      p2 %= WIDTH;
      res = p1 << p2;
      break;
    case LSHR:
      p2 %= WIDTH;
      res = p1 >> p2;
      break;
    case ASHR:
      p2 %= WIDTH;
      res = (word_t) (i1 >> p2);
      break;
    case EQ:
      if (p1 == p2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    case NE:
      if (p1 != p2) {
        res = 1;
      } else {
        res = 0;
      }
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
    case SLE:
      if (i1 <= i2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    case SLT:
      if (i1 < i2) {
        res = 1;
      } else {
        res = 0;
      }
      break;
    case MOD:
      assume(p2 != 0);
      res = p1 % p2;
      break;
    case IMPLIES:
      res = (p1 == 0) || (p2 != 0);
      break;
    case MIN:
      res = (p1 < p2) ? p1 : p2;
      break;
    case MAX:
      res = (p1 > p2) ? p1 : p2;
      break;
    case ITE:
      res = (p1 != 0) ? p2 : p3;
      break;
#ifdef FLOAT
    case FPLUS:
      fi.f = f1 + f2;
      res = fi.x;
      break;
    case FMINUS:
      fi.f = f1 - f2;
      res = fi.x;
      break;
    case FMUL:
      fi.f = f1 * f2;
      res = fi.x;
      break;
    case FDIV:
      assume(fpclassify(f2) != FP_ZERO);
      fi.f = f1 / f2;
      res = fi.x;
      break;
#endif // FLOAT
    case ISINF:
      res = (p1 == WORDMASK);
      break;
    case NOTINF:
      res = (p1 != WORDMASK);
      break;

    default:
      assume(0);
      break;
    }

#ifdef SEARCH
    res &= WORDMASK;
#endif

    A[ARGBASE + i] = res;
  }

  for (i = 0; i < NRES && i < LEN(prog); i++) {
    results[i] = A[ARGBASE + LEN(prog) - i - 1];
  }
}
