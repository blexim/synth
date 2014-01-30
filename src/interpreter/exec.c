#include "synth.h"
#include "exec.h"
#include "library.h"

#include <math.h>

void exec(prog_t *prog, word_t args[NARGS], word_t results[NRES]) {
  word_t lib[LIBSZ*3];
  int i;

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
      a = lib[(in1 - NARGS) * 3];
    }

    if (in2 < NARGS) {
      b = args[in2];
    } else {
      b = lib[(in2 - NARGS) * 3];
    }

    __CPROVER_assume(a == lib[(i*3) + 1]);
    __CPROVER_assume(b == lib[(i*3) + 2]);
  }

  results[0] = lib[prog->output_var * 3];
}
