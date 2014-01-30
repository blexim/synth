#ifndef SYNTH_H

#ifndef LIBSZ
 #define LIBSZ 16
#endif

#ifndef WIDTH
 #define WIDTH 32
#endif

#ifndef NARGS
 #define NARGS 1
#endif

#ifndef NRES
 #define NRES 1
#endif

typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
typedef __CPROVER_bitvector[WIDTH] sword_t;
typedef float fword_t;

typedef struct prog {
  unsigned int inst_perm[LIBSZ];
  unsigned int op_perm[LIBSZ*2];
  unsigned int output_var;
} prog_t;

typedef union fi {
  word_t x;
  fword_t f;
} fi_t;

extern prog_t prog;

void exec(prog_t *prog, word_t args[NARGS], word_t res[NRES]);
void test(prog_t *prog, word_t args[NARGS]);

int check(word_t args[NARGS], word_t res[NRES]);
void tests(prog_t *prog);

int exclude(prog_t *prog);
int wellformed(prog_t *prog);

#endif // SYNTH_H
