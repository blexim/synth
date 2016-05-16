#include "synth.h"
#include "network.h"

#define GW 2
#define N 4

#define IS_NODE(x) ((x) <= N && (x) > 0)
#define INF 15

int sec(word_t x, word_t y) {
  return 
    (x==1 && y==2) ||
    (x==2 && y==1) ||
    (x==2 && y==3) ||
    (x==3 && y==4);
}

/* int edge(word_t x, word_t y) { */
/*   return  */
/*     (x==1 && y==2) || */
/*     (x==2 && y==3) || */
/*     (x==3 && y==2) || */
/*     (x==4 && y==2); */
/* } */

word_t exec1(prog_t *prog, word_t node) {
  word_t args[NARGS];
  word_t res[NRES];
  word_t i;

  for (i = 0; i < NARGS; i++) {
    args[i] = 0;
  }

  args[0] = node;
  exec(prog, args, res);

  return res[0];
}

word_t exec2(prog_t *prog, word_t node1, word_t node2) {
  word_t args[NARGS];
  word_t res[NRES];
  word_t i;

  for (i = 0; i < NARGS; i++) {
    args[i] = 0;
  }

  args[0] = node1;
  args[1] = node2;
  exec(prog, args, res);

  return res[0];
}


#define dist(x) exec1(&solution->progs[0], (x))
#define pred(x) exec1(&solution->progs[1], (x))
#define edge(x,y) exec2(&solution->progs[2], x, y)

int check(solution_t *solution, word_t args[NARGS]) {
  word_t res[NRES];
  word_t x = args[0];
  word_t y;

  if (dist(GW) != 0) {
    return 0;
  }

  if (edge(3, 2)) {
    return 0;
  }

  if (x != GW && IS_NODE(x) && dist(x) < INF) {
    y = pred(x);

    if (!IS_NODE(y)) {
      return 0;
    }

    if (!edge(x, y)) {
      return 0;
    }

    if (dist(y) >= dist(x)) {
      //if (dist(y) + 1 != dist(x)) {
      return 0;
    }
  }

  if (IS_NODE(x) && dist(x) >= INF) {
    return 0;
  }

  return 1;
}
