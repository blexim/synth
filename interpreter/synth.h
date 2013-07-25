#ifndef SYNTH_H

#ifndef SZ
 #define SZ 5
#endif

#ifndef WIDTH
 #define WIDTH 32
#endif

#ifndef NARGS
 #define NARGS 1
#endif

#ifndef CONSTS
 #define CONSTS SZ
#endif

// The width of a pointer
#ifndef PWIDTH
 #define PWIDTH WIDTH
#endif

const int MAXOPCODE = 13;

// This has to be the smallest integer such that 2**(OPLEN) >= MAXOPCODE
#define OPLEN 4


typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
typedef __CPROVER_bitvector[WIDTH] sword_t;

typedef unsigned __CPROVER_bitvector[PWIDTH] param_t;
typedef unsigned __CPROVER_bitvector[OPLEN] op_t;
typedef unsigned __CPROVER_bitvector[1] bit_t;

typedef struct prog {
  op_t ops[SZ];
  param_t params[SZ*2];
  word_t consts[CONSTS];
} prog_t;

word_t exec(word_t args[NARGS], prog_t *prog);
void test(word_t args[NARGS], prog_t *prog);

int check(word_t args[NARGS], word_t z);
void tests(prog_t *prog);

void hint(prog_t *prog);
void exclude(prog_t *prog);

#endif // SYNTH_H