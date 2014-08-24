/* find */

#include "synth.h"
#include "heaplib.h"

void prefix(word_t args[NARGS]) {
  word_t tmp = args[0];
  word_t a = args[1];
  word_t x = args[2];

  tmp = x;

  args[0] = tmp;
  args[1] = a;
  args[2] = x;
}

int guard(word_t args[NARGS]) {
  return args[0] != 0 && args[0] != args[1];
}

int body(word_t args[NARGS]) {

  word_t tmp = args[0];
  word_t a = args[1];
  word_t x = args[2];

  if (tmp == 0) {
    return 0;
  }

  tmp = deref(tmp, args);

  args[0] = tmp;

  return 1;
}

int assertion(word_t args[NARGS]) {
  return path(args[2], args[0], args);
}


/* int inv(solution_t *sol, word_t args[NARGS]) { */
/*   word_t res[NRES]; */

/*   exec(&sol->progs[0], args, res); */

/*   return res[0]; */
/* } */

/* int check(solution_t *sol, word_t args[NARGS]) { */
/*   word_t res[NRES]; */


/*   word_t tmp = args[0]; */
/*   word_t a = args[1]; */
/*   word_t x = args[2]; */

  /* for (i = 0; i < NARGS; i++) { */
  /*   if (!is_ptr(args[i])) { */
  /*     return 1; */
  /*   } */
  /* } */


/*     if (tmp == 0) { */
/*        return 0; */
/*     } */

/*     tmp = deref(tmp, args); */

/*     word_t args2[NARGS]; */

/*     args2[0] = tmp; */

/*     for (int i = 1; i < NARGS; i++) { */
/*       args2[i] = args[i]; */
/*     } */

/*     if (!inv(sol, args2)) { */
/*       return 0; */
/*     } */
/*   } */

/*   if(inv(sol, args) && (tmp == 0 || tmp == a)) { */
/*     if(!path(x, tmp, args)) */
/*       return 0; */
/*   } */

/*   if(tmp == x) { */
/*     if(!inv(sol, args)) */
/*       return 0; */
/*   } */

/*   return 1; */
/* } */



