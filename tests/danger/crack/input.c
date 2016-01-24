#include "state.h"

extern int prefix(state_t *in, state_t *out);
extern int guard(state_t *state);
extern int body(state_t *in, state_t *out_vars);
extern int assertion(state_t *state);

int inv(state_t *state);
int skolem(state_t *in, state_t *out);
int rank(state_t *state);

int check(state_t *state) {
  state_t tmp, pre_vars, post_vars;
  int i;

  if (!prefix(state, &post_vars)) {
    return 0;
  }

  if (!inv(&post_vars)) {
    return 0;
  }

  return 1;
}

int main(void) {
  state_t state;

  assert(!check(&state));
}
