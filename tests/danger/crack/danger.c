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

  tmp = *state;

  if (inv(&tmp) && guard(&tmp)) {
    unsigned int r1, r2;

    r1 = rank(&tmp);

    skolem(&tmp, &pre_vars);
    body(&pre_vars, &post_vars);

    r2 = rank(&post_vars);

    if (r1 == 0) {
      return 0;
    }

    if (r1 <= r2) {
      return 0;
    }

    if (!inv(&post_vars)) {
      return 0;
    }
  }

  pre_vars = *state;

  if (inv(&pre_vars) && !guard(&pre_vars)) {
    if (assertion(&pre_vars)) {
      return 0;
    }
  }

  return 1;
}

int main(void) {
  state_t state;

  assert(check(&state));
}
