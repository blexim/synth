#include "state2.h"

int skolem(state_t *in, state_t *out) {
  *out = *in;
  out->nondet = out->i == out->j;
}

int inv(state_t *state) {
  return state->i <= state->j && state->j <= 1000000;
}

int rank(state_t *state) {
  return 1000000 - state->i;
}

int prefix(state_t *in, state_t *out) {
  *out = *in;
  out->i = 0;
}

int guard(state_t *state) {
  return state->i < 1000000;
}

int body(state_t *in, state_t *out) {
  *out = *in;
  out->i++;

  if (out->nondet) {
    out->j++;
  }
}

int assertion(state_t *state) {
  return state->i != state->j;
}
