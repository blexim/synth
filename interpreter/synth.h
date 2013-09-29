#ifndef SYNTH_H

#ifndef SZ
 #define SZ 5
#endif

#ifndef WIDTH
 #define WIDTH 32
#endif

#ifndef MWIDTH
 #define MWIDTH 23
#endif

#ifndef NARGS
 #define NARGS 1
#endif

#ifndef NRES
 #define NRES 1
#endif

#ifndef CONSTS
 #define CONSTS SZ
#endif

// The width of a pointer
#ifndef PWIDTH
 #define PWIDTH WIDTH
#endif

#define MAXOPCODE 19

// This has to be the smallest integer such that 2**(OPLEN) >= MAXOPCODE
#define OPLEN 5

#ifndef SEARCH
  typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
  typedef __CPROVER_bitvector[WIDTH] sword_t;
  typedef __CPROVER_floatbv[WIDTH][MWIDTH] fword_t;
  //typedef float fword_t;

  typedef unsigned __CPROVER_bitvector[PWIDTH] param_t;
  typedef unsigned __CPROVER_bitvector[OPLEN] op_t;
  typedef unsigned __CPROVER_bitvector[1] bit_t;
#else
  typedef unsigned int word_t;
  typedef int sword_t;
  typedef float fword_t;

  typedef unsigned int param_t;
  typedef unsigned int op_t;
  typedef unsigned int bit_t;
#endif

#ifdef SEARCH
  #define __CPROVER_assume(x) do {\
    if (!(x)) execok = 0; \
  } while(0)
#endif


typedef struct prog {
  op_t ops[SZ];
  param_t params[SZ*2];
  word_t consts[CONSTS];
} prog_t;

typedef union fi {
  word_t x;
  fword_t f;
} fi_t;

extern prog_t prog;
extern int execok;

void exec(prog_t *prog, word_t args[NARGS], word_t res[NRES]);
void test(prog_t *prog, word_t args[NARGS]);

int check(word_t args[NARGS], word_t res[NRES]);
void tests(prog_t *prog);

void hint(prog_t *prog);
int exclude(prog_t *prog);

#endif // SYNTH_H
