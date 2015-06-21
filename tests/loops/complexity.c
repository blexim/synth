#include "synth.h"

#define BVAR (NARGS-1)

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t args[NARGS]);
extern int body(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int assertion(word_t args[NARGS]);

int inv(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
}

word_t bound(prog_t *prog, word_t args[NARGS]) {
  word_t res[NRES];

  exec(prog, args, res);

  return res[0];
}

int check(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  prog_t *prog = &solution->progs[0];
  prog_t *bound_prog = &solution->progs[1];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  pre_vars[BVAR] = 0;

  if (prefix(pre_vars, post_vars)) {
    post_vars[BVAR] = 0;
    post_vars[BVAR] = bound(bound_prog, post_vars);
    
    if (!inv(prog, post_vars)) {
      printf("BAM1\n");
      return 0;
    }      
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (guard(pre_vars) && pre_vars[BVAR] > 0 && inv(prog, pre_vars)) {
    if (!body(pre_vars, post_vars)) {
      printf("BAM2\n");
      return 0;
    }

    post_vars[BVAR] = pre_vars[BVAR] - 1;

    if (!inv(prog, post_vars)) {
      printf("BAM3\n");
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (guard(pre_vars) && pre_vars[BVAR] <= 0 && inv(prog, pre_vars)) {
      printf("BAM4\n");
      return 0;
  }

  return 1;
}

