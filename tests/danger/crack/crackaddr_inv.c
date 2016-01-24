#include "state.h"

int inv(state_t *state) {
  if (state->upperlimit < BUFFERSIZE) {
    if (state->c == 0) {
      return 0;
    } else if (state->c != 40 && state->c != 41) {
      return 0;
    }
  }

  return 1;
}

int skolem(state_t *in, state_t *out) {
  *out = *in;

  if (out->upperlimit < BUFFERSIZE) {
    if (out->roundquote) {
      out->nc = ')';
    } else {
      out->nc = '(';
    }
  } else {
    out->nc = 'A';
  }
}

int rank(state_t *state) {
  return BUFFERSIZE + 51 - state->p;
}
