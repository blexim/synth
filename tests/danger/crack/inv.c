#include "state.h"

int inv(state_t *state) {
  char c = state->c;

  if (state->upperlimit < BUFFERSIZE) {
    if (idx >= BUFFERSIZE) {
      return 0;
    }

    char nc = state->input[state->p];

    if ((c == '(' && nc == ')') || (c == ')' && nc == '(')) {
      return 1;
    } else {
      return 0;
    }
  } else {
    switch (c) {
      case '(':
      case ')':
      case '<':
      case '>':
      case '\0':
        return 0;
      default:
        return 1;
    }
  }

  return 1;
}

int skolem(state_t *in, state_t *out) {
  *out = *in;
}

int rank(state_t *state) {
  return 1;
}
