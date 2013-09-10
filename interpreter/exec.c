#include "synth.h"
#include "exec.h"

int execok;

#define push(x) (stack[sp++] = (x))

#define pop(x) (stack[--sp])

word_t exec(word_t args[NARGS], prog_t *prog) {
  op_t op;
  param_t a;
  word_t p1, p2, res, result;
  sword_t i1, i2;
  word_t stack[SZ+NARGS];
  int sp = 0;

  unsigned int i;

  execok = 1;

  for (i = 0; i < NARGS; i++) {
    push(args[i]);
  }

  for (i = 0; i < SZ; i++) {
    op = prog->ops[i];
    a = prog->params[i];

    switch(op) {
    case PLUS:
      p1 = pop();
      p2 = pop();
      push(p1 + p2);
      break;
    case MINUS:
      p1 = pop();
      p2 = pop();
      push(p1 - p2);
      break;
    case MUL:
      p1 = pop();
      p2 = pop();
      push(p1 * p2);
      break;
    case DIV:
      p1 = pop();
      p2 = pop();
#ifdef SYNTH
      __CPROVER_assume(p2 != 0);
#elif defined(SEARCH)
      if (p2 == 0) {
        execok = 0;
        return 0;
      }
#else
      assert(p2 != 0);
#endif
      push(p1 / p2);
      break;
    case NEG:
      p1 = pop();
      push(-p1);
      break;
    case AND:
      p1 = pop();
      p2 = pop();
      push(p1 & p2);
      break;
    case OR:
      p1 = pop();
      p2 = pop();
      push(p1 | p2);
      break;
    case XOR:
      p1 = pop();
      p2 = pop();
      push(p1 ^ p2);
      break;
    case NOT:
      p1 = pop();
      push(~p1);
      break;
    case SHL:
      p1 = pop();
      p2 = pop();
      push(p1 << p2);
      break;
    case LSHR:
      p1 = pop();
      p2 = pop();
      push(p1 >> p2);
      break;
    case ASHR:
      i1 = pop();
      i2 = pop();
      push((word_t) (i1 >> i2));
      break;
    case LE:
      p1 = pop();
      p2 = pop();

      if (p1 <= p2) {
        push(1);
      } else {
        push(0);
      }
      break;
    case LT:
      p1 = pop();
      p2 = pop();

      if (p1 < p2) {
        push(1);
      } else {
        push(0);
      }
      break;
    case PUSH:
      if (a < NARGS) {
        push(args[a]);
      } else {
        push(prog->consts[a - NARGS]);
      }
      break;
    case DUP:
      p1 = pop();
      push(p1);
      push(p1);
      break;
    case SWAP:
      p1 = pop();
      p2 = pop();
      push(p1);
      push(p2);
    default:
#ifndef SEARCH
      __CPROVER_assume(0);
#endif
      break;
    }
  }

  result = pop();

  return result;
}
