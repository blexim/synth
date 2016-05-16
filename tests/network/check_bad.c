#include "synth.h"
#include "network.h"


int sec(word_t x, word_t y) {
  return 
    (x==1 && y==2) ||
    (x==2 && y==1) ||
    (x==2 && y==3) ||
    (x==3 && y==4);
}

int edge(word_t x, word_t y) {
  return 
    (x==1 && y==2) ||
    (x==2 && y==3) ||
    (x==3 && y==4);
}



int check(solution_t *solution, word_t args[NARGS]) {
  word_t res[NRES];
  word_t access_x, access_y, access_z;
  word_t args_y[NARGS], args_z[NARGS];

  word_t n = 5;

  exec(&solution->progs[0], args, res);
  access_x = res[0];
  
  // base case
  if(edge(args[0], 2) && sec(args[0], 2) && sec(2, args[0])) {
    if(access_x == 0)
      return 0;
  }

  // inductiveness

  word_t y;
  args_y[0] = y; // nondet
  exec(&solution->progs[0], args_y, res);
  access_y = res[0];

  if(/*args[0] <= n && args[1] <= n &&*/ edge(args[0],y) && sec(args[0],y) && sec(y,args[0]) && access_y == 1) {
    if(access_x == 0)
      return 0;
  }

  /* word_t z; */
  /* args_z[0] = z; // nondet */
  /* exec(&solution->progs[0], args_z, res); */
  /* access_z = res[0]; */

  /* if(!edge(args[0],z) || !sec(args[0],z) || !sec(z,args[0])) { */
  /*   if(access_z != 0) */
  /*     return 0; */
  /* } */

  return 1;

}
