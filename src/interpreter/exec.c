#include "synth.h"
#include "exec.h"

#include <math.h>

volatile int execok;

void exec(prog_t *prog, word_t args[NARGS], word_t results[NRES]) {
  op_t op;
  param_t a1, a2;
  word_t p1, p2, res;
  sword_t i1, i2;
  word_t A[SZ + NARGS + CONSTS];

#ifdef FLOAT
  fword_t f1, f2;
  fi_t fi;
#endif

  unsigned int i;

  for (i = 0; i < CONSTS; i++) {
    A[i] = prog->consts[i];
  }

  for (i = 0; i < NARGS; i++) {
    A[CONSTS + i] = args[i];
  }

  execok = 1;

  for (i = 0; i < SZ; i++) {
    op = prog->ops[i];
    a1 = prog->params[2*i];
    a2 = prog->params[2*i + 1];

    p1 = A[a1];
    p2 = A[a2];

    i1 = p1;
    i2 = p2;

#ifdef SEARCH
    i1 <<= (32 - WIDTH);
    i1 >>= (32 - WIDTH);

    i2 <<= (32 - WIDTH);
    i2 >>= (32 - WIDTH);
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
#ifdef SYNTH
      __CPROVER_assume(p2 != 0);
#elif defined(SEARCH)
      if (p2 == 0) {
        execok = 0;
        return;
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
      p2 %= WIDTH;
      res = p1 << p2;
      break;
    case LSHR:
      p2 %= WIDTH;
      res = p1 >> p2;
      break;
    case ASHR:
      i2 %= WIDTH;
      res = (word_t) (i1 >> i2);
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
#ifdef SYNTH
      __CPROVER_assume(p2 != 0);
#elif defined(SEARCH)
      if (p2 == 0) {
        execok = 0;
        return;
      }
#endif
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
#ifdef SYNTH
      __CPROVER_assume(fpclassify(f2) != FP_ZERO);
#elif defined(SEARCH)
      if (fpclassify(f2) == FP_ZERO) {
        execok = 0;
        return;
      }
#else
      assert(fpclassify(f2) != FP_ZERO);
#endif
      fi.f = f1 / f2;
      res = fi.x;
      break;
#endif // FLOAT

    default:
#ifndef SEARCH
      __CPROVER_assume(0);
#endif
      break;
    }

#ifdef SEARCH
    res &= ((1 << WIDTH) - 1);
#endif

    A[NARGS + CONSTS + i] = res;
  }

  for (i = 0; i < NRES; i++) {
    results[i] = A[NARGS + CONSTS + SZ - NRES + i];
  }
}
