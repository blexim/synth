#include "heap.h"

#include <string.h>

static void destructive_kernel(abstract_heapt *heap);

static void copy_abstract(abstract_heapt *pre,
                          abstract_heapt *post) {
  //memcpy(post, pre, sizeof(abstract_heapt));
  *post = *pre;
}

/*
 * Dereference p -- which node does p point to?
 */
static node_t deref(abstract_heapt *heap,
                    ptr_t p) {
  // Ensure p is a real pointer.
  __CPROVER_assume(p < NPROG);
  return heap->ptr[p];
}

/*
 * Next operator -- which node is in n's next pointer?
 */
static node_t next(abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  __CPROVER_assume(n < NABSNODES);
  return heap->succ[n];
}

/*
 * How far away is n's successor?
 */
static word_t dist(abstract_heapt *heap,
                   node_t n) {
  __CPROVER_assume(n < NABSNODES);
  return heap->dist[n];
}


/*
 * Find the reachable nodes in the heap & return the number found.
 */
int find_reachable(abstract_heapt *heap,
                   word_t is_reachable[NABSNODES]) {
  word_t nreachable = 0;

  memset(is_reachable, 0, NABSNODES * sizeof(word_t));

  // We're going to do a mark-and-sweep garbage collection.
  // First mark all of the program variables as reachable.
  ptr_t p;
  node_t n;

  for (p = 0; p < NPROG; p++) {
    n = deref(heap, p);
    is_reachable[n] = 1;
    nreachable++;
  }

  // Now do the transitive closure of the reachability relation.
  node_t i, j;

  for (i = 1; i < NABSNODES; i++) {
    for (j = 1; j < NABSNODES; j++) {
      if (is_reachable[j]) {
        n = next(heap, j);

        if (!is_reachable[n]) {
          is_reachable[n] = 1;
          nreachable++;
        }
      }
    }
  }

  return nreachable;
}

/*
 * x = n;
 *
 * x is a pointer, n is a graph node.
 */
static void destructive_assign_ptr(abstract_heapt *heap,
                                   ptr_t x,
                                   node_t n) {
  __CPROVER_assume(x < NPROG);
  __CPROVER_assume(n < NABSNODES);
  heap->ptr[x] = n;
}

/*
 * x.n = y;
 *
 * x and y are nodes.
 */
static void destructive_assign_next(abstract_heapt *heap,
                                    node_t x,
                                    node_t y,
                                    word_t dist) {
  __CPROVER_assume(x < NABSNODES);
  __CPROVER_assume(y < NABSNODES);
  heap->succ[x] = y;
  heap->dist[x] = dist;
}

/*
 * x = y;
 *
 * x and y are pointers.
 */
void abstract_assign(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  __CPROVER_assume(x < NPROG);
  __CPROVER_assume(y < NPROG);

  copy_abstract(pre, post);

  node_t py = deref(post, y);
  destructive_assign_ptr(post, x, py);

  //destructive_kernel(post);
}

/*
 * Allocate a new node.
 */
static node_t destructive_alloc(abstract_heapt *heap) {
#if 0
  word_t is_reachable[NABSNODES];
  word_t nreachable = find_reachable(heap, is_reachable);
  node_t n;

  for (n = 0; n < NABSNODES; n++) {
    if (!is_reachable[n]) {
      return n;
    }
  }
#endif
  node_t n;

  __CPROVER_assume(heap->nnodes < NABSNODES);
  return heap->nnodes++;
}

/*
 * x = new();
 */
void abstract_new(abstract_heapt *pre,
                  abstract_heapt *post,
                  ptr_t x) {
  __CPROVER_assume(x < NPROG);

  copy_abstract(pre, post);

  // Just allocate a new node and have x point to it.
  node_t n = destructive_alloc(post);
  destructive_assign_next(post, n, null_node, 1);
  destructive_assign_ptr(post, x, n);

  //destructive_kernel(post);
}

/*
 * x = y->n
 */
void abstract_lookup(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  __CPROVER_assume(x < NPROG);
  __CPROVER_assume(y < NPROG);

  node_t py = deref(pre, y);
  node_t yn = next(pre, py);

  word_t y_yn_dist = dist(pre, py);

  __CPROVER_assume(py != null_node);

  __CPROVER_assume(y_yn_dist > 0);

  copy_abstract(pre, post);


  // Two cases: 
  //
  // (1): y has a direct successor, i.e. y -1> z
  // (2): y's successor is some distance > 1 away, i.e. y -k-> z
  if (y_yn_dist == 1) {
    // Case 1:
    //
    // y's successor is one step away, so now x points to that
    // successor -- this is just a simple assign to the successor node.
    destructive_assign_ptr(post, x, yn);
    //destructive_kernel(post);
  } else {
    // Case 2:
    //
    // y's successor is more than one step away, so we need to introduce
    // an intermediate node n, which will become y's successor and which x
    // will point to, i.e.
    //
    // Pre state:
    //
    // y -k> z
    //
    // Post state:
    //
    // y -1> x -(k-1)> z
    //
    // Begin by allocating a new node between y and yn.
    node_t n = destructive_alloc(post);
    word_t new_dist = s_sub(y_yn_dist, 1);
    destructive_assign_next(post, n, yn, new_dist);

    // Reassign y's next pointer to the newly allocated node.
    destructive_assign_next(post, py, n, 1);

    // And make x point to the new node.
    destructive_assign_ptr(post, x, n);

    //destructive_kernel(post);
  }
}

/*
 * x->n = y;
 */
void abstract_update(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  __CPROVER_assume(x < NPROG);
  __CPROVER_assume(y < NPROG);

  copy_abstract(pre, post);

  node_t px = deref(post, x);
  node_t xn = next(post, x);

  __CPROVER_assume(px != null_node);

  node_t py = deref(post, y);

  destructive_assign_next(post, px, py, 1);
  //destructive_kernel(post);
}

/*
 * Check that the heap is well formed.
 */
int valid_abstract_heap(abstract_heapt *heap) {
  // NULL points to the null node.
  if (deref(heap, null_ptr) != null_node) {
    return 0;
  }

  // The null node doesn't point anywhere.
  if (next(heap, null_node) != null_node) {
    return 0;
  }

  if (dist(heap, null_node) != 0) {
    return 0;
  }

  // Each program variable points to a valid node.
  ptr_t p;

  for (p = 0; p < NPROG; p++) {
    if (deref(heap, p) >= heap->nnodes) {
      return 0;
    }
  }

  // Each node's next pointer points to a valid node.
  node_t n;

  for (n = 0; n < NABSNODES; n++) {
    if (next(heap, n) >= heap->nnodes) {
      return 0;
    }
  }

  // Each node, except null, is > 0 away from its successor.
  for (n = 0; n < NABSNODES; n++) {
    if (n != null_node && dist(heap, n) <= 0) {
      return 0;
    }

    if (dist(heap, n) >= INF) {
      return 0;
    }
  }

#if 1
  return is_minimal(heap);
#else
  return 1;
#endif
}

/*
 * Compute the heap facts, i.e. all the pairwise distances between program
 * variables.
 */
void consequences(abstract_heapt *heap,
                  heap_factst *facts) {
  word_t min_dists[NPROG][NABSNODES];
  ptr_t x, y;
  node_t n;
  word_t curr_dist;
  word_t i;

#if 1
  memset(min_dists, INF, NPROG*NABSNODES*sizeof(word_t));
#else
  for (x = 0; x < NPROG; x++) {
    for (n = 0; n < NABSNODES; n++) {
      min_dists[x][n] = INF;
    }
  }
#endif

  for (x = 0; x < NPROG; x++) {
    n = deref(heap, x);
    curr_dist = 0;
    min_dists[x][n] = 0;

    // First compute the distance from x to each heap node...
    for (i = 0; i < heap->nnodes && i < NABSNODES; i++) {
      curr_dist = s_add(curr_dist, dist(heap, n));
      n = next(heap, n);

#if 0
      min_dists[x][n] = min(min_dists[x][n], curr_dist);
#else
      if (min_dists[x][n] != INF) {
        // We've hit a cycle.
        break;
      }

      min_dists[x][n] = curr_dist;
#endif
    }

    // Now fill in the heap facts!
    for (y = 0; y < NPROG; y++) {
      n = deref(heap, y);
      facts->dists[x][y] = min_dists[x][n];
    }
  }
}

/*
 * Create an initial heap where everything points to null.
 */
void init_abstract_heap(abstract_heapt *heap) {
  node_t n;

  for (n = 0; n < NABSNODES; n++) {
    heap->succ[n] = null_node;
    heap->dist[n] = 1;
  }

  heap->succ[null_node] = null_node;
  heap->dist[null_node] = 0;

  ptr_t p;

  for (p = 0; p < NPROG; p++) {
    heap->ptr[p] = null_node;
  }
}

int is_minimal(abstract_heapt *heap) {
  word_t is_named[NABSNODES];
  memset(is_named, 0, sizeof(is_named));

  // Find all of the named nodes.
  ptr_t p;
  node_t n, m;

  for (p = 0; p < NPROG; p++) {
    n = deref(heap, p);
    is_named[n] = 1;
  }

  // Check that each node is reachable.
  word_t is_reachable[NABSNODES];
  word_t nreachable;

  nreachable = find_reachable(heap, is_reachable);

  if (heap->nnodes > nreachable) {
    return 0;
  }

  // Find the indegree of each node, restricted to just the reachable subgraph.
  word_t indegree[NABSNODES];
  memset(indegree, 0, sizeof(indegree));

  for (n = 0; n < NABSNODES; n++) {
    if (is_reachable[n]) {
      m = next(heap, n);
      indegree[m]++;
    }
  }

  // Check there are no unnamed, reachable nodes with indegree <= 1.
  for (n = 0; n < NABSNODES; n++) {
    if (!is_named[n] && is_reachable[n] && indegree[n] <= 1) {
      return 0;
    }
  }

  return 1;
}

/*
 * Remove node m by merging it into node n.
 *
 * Note: if there are any pointer into m, this is very unsafe, so
 * only do it if you've already checked m has indegree = 1.
 */
void destructive_merge_nodes(abstract_heapt *heap,
                             node_t n,
                             node_t m) {
  __CPROVER_assume(m == next(heap, n));

  // n->next = m->next
  heap->succ[n] = next(heap, m);

  // n->dist += m->dist
  heap->dist[n] = s_add(dist(heap, n), dist(heap, m));
}

/*
 * Reduce a graph down to its kernel.
 */
void destructive_kernel(abstract_heapt *heap) {
  word_t is_named[NABSNODES];
  memset(is_named, 0, sizeof(is_named));

  // Find all of the named nodes.
  ptr_t p;
  node_t n, m;

  for (p = 0; p < NPROG; p++) {
    n = deref(heap, p);
    is_named[n] = 1;
  }

  // Check that each node is reachable.
  word_t is_reachable[NABSNODES];
  word_t nreachable;

  nreachable = find_reachable(heap, is_reachable);

  // Find the indegree of each node, restricted to just the reachable subgraph.
  word_t indegree[NABSNODES];
  memset(indegree, 0, sizeof(indegree));

  for (n = 0; n < NABSNODES; n++) {
    if (is_reachable[n]) {
      m = next(heap, n);
      indegree[m]++;
    }
  }

  // Merge as many nodes as possible.
  word_t i;

  for (i = 0; i < NABSNODES; i++) {
    for (n = 1; n < NABSNODES; n++) {
      if (is_reachable[n]) {
        m = next(heap, n);

        if (!is_named[m] && indegree[m] <= 1) {
          destructive_merge_nodes(heap, n, m);
          is_reachable[m] = 0;
        }
      }
    }
  }
}
