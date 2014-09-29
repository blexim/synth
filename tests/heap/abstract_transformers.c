#include "heapabstract.h"

void abstract_assign(unsigned int x,
                     unsigned int y,
                     abstract_heapt pre,
                     abstract_heapt post) {
  int i;

  for (i = 0; i < ABSSIZE; i++) {
    post[i] = pre[i];
  }

  unsigned int z;

  for (z = 0; z < NPROG; z++) {
    post[abs_idx(x, z)] = pre[abs_idx(y, z)];
    post[abs_idx(z, x)] = pre[abs_idx(z, y)];

    post[cut_idx(x, z)] = pre[cut_idx(y, z)];
    post[cut_idx(z, x)] = pre[cut_idx(z, y)];

    post[cut_cut_idx(x, z)] = pre[cut_cut_idx(y, z)];
    post[cut_cut_idx(z, x)] = pre[cut_cut_idx(z, x)];

    post[cycle_idx(x)] = pre[cycle_idx(y)];
    post[cycle_dist_idx(x)] = pre[cycle_dist_idx(y)];
  }

  post[abs_idx(x ,x)] = 0;
  post[cut_idx(x ,x)] = 0;
  post[cut_cut_idx(x ,x)] = 0;
}
