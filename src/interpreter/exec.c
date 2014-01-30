#include "synth.h"
#include "exec.h"
#include "library.h"

void exec(prog_t *prog, word_t args[NARGS], word_t results[NRES]) {
  word_t lib[LIBSZ*3];
  int i;
  int idx;

  // The library constraint.
  assume_library(lib);

  // The connectedness constraint.
  for (i = 0; i < LIBSZ; i++) {
    int in1 = prog->op_perm[i*2];
    int in2 = prog->op_perm[(i*2) + 1];

    word_t a, b;

    if (in1 < NARGS) {
      a = args[in1];
    } else {
      idx = prog->inst_perm[in1 - NARGS];
      a = lib[idx * 3];
    }

    if (in2 < NARGS) {
      b = args[in2];
    } else {
      idx = prog->inst_perm[in2 - NARGS];
      b = lib[idx * 3];
    }
  
    idx = prog->inst_perm[i];

    __CPROVER_assume(a == lib[(idx*3) + 1]);
    __CPROVER_assume(b == lib[(idx*3) + 2]);
  }

  idx = prog->inst_perm[prog->output_var];
  results[0] = lib[idx * 3];
}
