#include "synth.h"
#include "exec.h"

int exclude(prog_t *prog) {
  int i;
  int stacksize = NARGS;

  for (i = 0; i < SZ; i++) {
    op_t op;
    param_t p;

    op = prog->ops[i];
    p = prog->params[i];

    if (op == PUSH) {
      if (p >= (NARGS + CONSTS)) {
        return 1;
      }
    } else {
      if (p != 0) {
        return 1;
      }
    }

    switch (op) {
    case PUSH:
      stacksize++;
      break;
    case DUP:
      if (stacksize < 1) {
        return 1;
      }
      stacksize++;
      break;
    case NEG:
    case NOT:
      if (stacksize < 1) {
        return 1;
      }
      break;
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case AND:
    case OR:
    case XOR:
    case SHL:
    case LSHR:
    case ASHR:
    case LE:
    case LT:
      if (stacksize < 2) {
        return 1;
      }
      stacksize--;
      break;
    default:
      return 1;
    }
  }

  for (i = 0; i < CONSTS-1; i++) {
    if (prog->consts[i] >= prog->consts[i+1]) {
      return 1;
    }
  }

  return 0;
}
