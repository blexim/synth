#include "heapabstract.h"

void copy_abstract(abstract_heapt *pre,
                   abstract_heapt *post) {
  word_t x, y;

  for (x = 0; x < NPROG; x++) {
    post->stem[x] = pre->stem[x];
    post->cycle[x] = pre->cycle[x];

    for (y = 0; y < NPROG; y++) {
      post->dist[x][y] = pre->dist[x][y];
      post->cut[x][y] = pre->cut[x][y];
      pre->cut_cut[x][y] = pre->cut_cut[x][y];
    }
  }
}

void abstract_assign(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post) {
  int i;

  copy_abstract(pre, post);

  unsigned int z;

  for (z = 0; z < NPROG; z++) {
    post->dist[x][z] = pre->dist[y][z];
    post->dist[z][x] = pre->dist[z][y];

    post->cut[x][z] = pre->cut[y][z];
    post->cut[z][x] = pre->cut[z][y];

    post->cut_cut[x][z] = pre->cut_cut[y][z];
    post->cut_cut[z][x] = pre->cut_cut[z][y];
  }

  post->dist[x][x] = 0;
  post->cut[x][x] = 0;
  post->cut_cut[x][x] = 0;
}
