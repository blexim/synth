#include "state.h"

void body(state_t *a, state_t *b);

void lemma1() {
  state_t a, b, c;

  a.idx = 0;
  a.p = 0;
  a.roundquote = 0;
  __CPROVER_assume(a.upperlimit >= 0 && a.upperlimit <= BUFFERSIZE+50);
  body(&a, &b);
  body(&b, &c);

  __CPROVER_assume(c.upperlimit > a.upperlimit &&
      c.quotation == a.quotation &&
      c.roundquote == a.roundquote);

  assert(0);
}

int in_range(int x) {
  return x >= 0 && x < BUFFERSIZE;
}

int candidate_inv(state_t state) {
  return in_range(state.p) && in_range(state.idx) &&
    state.upperlimit >= 0 &&
    state.roundquote == 0 &&
    state.quotation == 0;
}

int pump_guard(state_t state) {
  return in_range(state.p) && state.upperlimit < BUFFERSIZE;
}

void pump() {
  state_t a, b, c;

  __CPROVER_assume(candidate_inv(a));
  __CPROVER_assume(pump_guard(a));

  __CPROVER_assume(a.c == 40 && a.input[a.p] == 41);

  body(&a, &b);
  body(&b, &c);

  if (guard(&c)) {
    assert(candidate_inv(c) || !pump_guard(c));
    assert(c.upperlimit > a.upperlimit);
  }
}

void establish_upperlimit() {
  state_t state;

  __CPROVER_assume(candidate_inv(state) && !pump_guard(state));
  assert(state.upperlimit >= BUFFERSIZE);
}
