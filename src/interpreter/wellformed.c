#include "synth.h"
#include "exec.h"

#define ISCONST(x) (x < CONSTS)

void wellformed(prog_t *prog) {
  int i, j;

  for (i = 0; i < LIBSZ; i++) {
    __CPROVER_assume(prog->inst_perm[i] >= 0 &&
        prog->inst_perm[i] < LIBSZ);

    for (j = i+1; j < LIBSZ; j++) {
      __CPROVER_assume(prog->inst_perm[i] != prog->inst_perm[j]);
    }
  }

  for (i = 0; i < LIBSZ; i++) {
    int in1 = prog->op_perm[2*i];
    int in2 = prog->op_perm[(2*i) + 1];

    __CPROVER_assume(in1 >= 0 && in1 < (i + NARGS));
    __CPROVER_assume(in2 >= 0 && in2 < (i + NARGS));
  }

  __CPROVER_assume(prog->output_var >= 0 && prog->output_var < LIBSZ);
}
