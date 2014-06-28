#include "synth.h"


void interchangeObs(word_t* src, word_t* dest)
{
  *src = *src ^ *dest;

  if (*src == (*src ^ *dest)) {
    *src = *src ^ *dest;

    if (*src == (*src ^ *dest)) {
      *dest = *src ^ *dest;
      
      if (*dest == (*src ^ *dest)) {
        *src = *dest ^ *src;
        return;
      } else {
        *src = *src ^ *dest;
        *dest = *src ^ *dest;
        return;
      } 
    } else
      *src = *src ^ *dest;
  }
  
  *dest = *src ^ *dest;
  *src = *src ^ *dest;

  return;
}

int check(solution_t *solution, word_t args[2]) {
  word_t res[NRES];
  exec(&solution->progs[0], args, res);

  word_t src = args[0];
  word_t dest = args[1];

  interchangeObs(&src, &dest);

  return (src == res[0] && dest == res[1]);
}
