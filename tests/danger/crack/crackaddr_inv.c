#include "state.h"

int inv(state_t *state) {
  if (state->idx >= BUFFERSIZE) {
    return 1;
  }

  if (state->c != 'A' && state->c != '(' && state->c != ')') {
    return 0;
  }

  if (state->c == '<' || state->c == '>') {
    return 0;
  }

  if (state->upperlimit > BUFFERSIZE && state->c != 'A') {
    return 0;
  }

  if (state->quotation) {
    return 0;
  }

  if (state->roundquote != 0 && state->roundquote != 1) {
    return 0;
  }

  if (state->upperlimit > BUFFERSIZE + 10) {
    return 0;
  }

  if (state->upperlimit < BUFFERSIZE - 10) {
    return 0;
  }

  if (state->upperlimit < BUFFERSIZE) {
    printf("XX upperlimit too low");

    int slack = (state->upperlimit - state->idx + state->roundquote) / 2;

    if (slack < (BUFFERSIZE - state->upperlimit)) {
      return 0;
    }

    if (state->roundquote && state->c != 41) {
      return 0;
    } else if (!state->roundquote && state->c != 40) {
      return 0;
    }
  }

  if (state->idx >= state->upperlimit + state->roundquote) {
    printf("XX idx too high");
    return 0;
  }

  if (state->idx != state->p) {
    printf("XX idx != p");
    return 0;
  }

  if (state->idx < BUFFERSIZE && state->c == 0) {
    printf("XX c is null");
    return 0;
  }

  return 1;
}

int skolem(state_t *in, state_t *out) {
  *out = *in;

  if (out->upperlimit < BUFFERSIZE) {
    if (out->roundquote) {
      out->nc = '(';
    } else {
      out->nc = ')';
    }
  } else {
    out->nc = 'A';
  }
}

int rank(state_t *state) {
  return BUFFERSIZE + 51 - state->p;
}
