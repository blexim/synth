/**
 *
 * Specification of conditional termination 
 * 
 */

#include "synth.h"

extern int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]);
extern int guard(word_t in_vars[NARGS]);
extern int body(word_t in_vars[NARGS], word_t out_vars[NARGS]);

/**
 *
 * Evaluate a loop invariant (i.e. a supporting invariant for conditional termination).
 *
 * solution->progs[0] is the loop inv, args are the arguments. 
 * 
 */

int inv(solution_t *solution, word_t args[NARGS]) {
  word_t res[NRES];

  exec(&solution->progs[0], args, res);

  return res[0];
}


/**
 *
 * Evaluate a ranking function.
 *
 * solution->progs[1] is the ranking fct, args are the arguments. 
 * 
 */

void rank(solution_t *solution, word_t args[NARGS], word_t res[NRES]) {
  exec(&solution->progs[1], args, res);
}


/**
 * Check whether a ranking function is monotonically decreasing.
 *
 * rank1 and rank2 are two subsequent values of the ranking fct.
 *
 * NRES is the number of lexicographic components.
 *
 */
int cmp(word_t rank1[NRES], word_t rank2[NRES]) {
  int i;

  for (i = 0; i < NRES; i++) {
    if (rank1[i] < rank2[i]) {
      return -1;
    } else if (rank1[i] > rank2[i]) {
      return 1;
    }
  }

  return 0;
}


/**
 * Check whether a ranking function is bounded from below.
 *
 * NRES is the number of lexicographic components.
 *
 */
int nonzero(word_t rank[NRES]) {
  int i;

  for (i = 0; i < NRES; i++) {
    if (rank[i] > 0) {
      return 1;
    }
  }

  return 0;
}


/**
 *
 * Check whether a candidate solution is a ranking function
 * for the loop:
 *
 * prefix(x,x')
 * while(guard(x')) {
 *   body(x',x'')
 *  }
 *
 * Basically, if R is the candidate solution, x and x' are two subsequent program states, 
 * and W is the candidate supporting invariant, check that:
 *
 * prefix(x,x') & guard(x') => W(x') 
 * guard(x') & W(x') & body(x',x'') => R(x') > 0 & R(x') > R(x'') & W(x'')
 *
 *
 * solution is the candidate solution, args denote the initial values of the arguments (program vars).
 *
 * Return 1 if solution is a ranking function, 0 otherwise.
 *
 */


int check_temination(solution_t *solution, word_t args[NARGS]) {
  word_t pre_vars[NARGS], post_vars[NARGS];
  int i;

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  // prefix(x,x') => W(x') 
  if (prefix(pre_vars, post_vars)) {
    if (!inv(solution, post_vars)) {
      return 0;
    }
  }

  for (i = 0; i < NARGS; i++) {
    pre_vars[i] = args[i];
  }

  if (guard(pre_vars) && inv(solution, pre_vars)) {
    word_t rank1[NRES];
    word_t rank2[NRES];

    rank(solution, pre_vars, rank1);

    // R is bounded from below
    // guard(x) & W(x) => R(x) > 0 
    if (!nonzero(rank1)) {
      return 0;
    }

    body(pre_vars, post_vars);

    rank(solution, post_vars, rank2);

    // R is monotonically decreasing
    // guard(x) & W(x) & body(x,x') => R(x) > R(x') 
    if (cmp(rank1, rank2) <= 0) {
      return 0;
    }

    // inductiveness of W
    // guard(x) & W(x) & body(x,x') => W(x')
    if (!inv(solution, post_vars)) {
      return 0;
    }
  }

  return 1;
}


/**
 * The generic checking procedure
 */

int check(solution_t *solution, word_t args[NARGS]) {
  check_temination(solution, args);
}

