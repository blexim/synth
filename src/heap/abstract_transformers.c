#include "heap.h"

#include <string.h>

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
  assert(p < NPROG);
  return heap->ptr[p];
}

/*
 * Next operator -- which node is in n's next pointer?
 */
static node_t next(abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  assert(n < heap->nnodes);
  return heap->succ[n];
}

/*
 * How far away is n's successor?
 */
static word_t dist(abstract_heapt *heap,
                   node_t n) {
  assert(n < heap->nnodes);
  return heap->dist[n];
}



/*
 * Replace node n with node m, i.e. every pointer that used to
 * point to n will now point to m.
 */
static void destructive_move_node(abstract_heapt *heap,
                                  node_t n,
                                  node_t m) {
  assert(n < heap->nnodes);
  assert(m < heap->nnodes);

  if (n == m) {
    // No need to do anything!
    return;
  }

  node_t old_succ = next(heap, n);
  node_t old_dist = dist(heap, n);

  ptr_t p;

  // First reassign the program variables...
  for (p = 0; p < NPROG; p++) {
    if (deref(heap, p) == n) {
      heap->ptr[p] = m;
    }
  }

  node_t x;
  // Now reassign the "next" pointers for each node.
  for (x = 0; x < heap->nnodes && x < NABSNODES; x++) {
    if (next(heap, x) == n) {
      heap->succ[x] = m;
    }
  }

  heap->succ[m] = old_succ;
  heap->dist[m] = old_dist;
}

/*
 * Find the reachable nodes in the heap & return the number found.
 */
int find_reachable(abstract_heapt *heap,
                   node_t reachable_nodes[NABSNODES]) {
  word_t is_reachable[NABSNODES];

  memset(is_reachable, 0, sizeof(is_reachable));

  // We're going to do a mark-and-sweep garbage collection.
  // First mark all of the program variables as reachable.
  ptr_t p;
  node_t n;

  for (p = 0; p < NPROG; p++) {
    n = deref(heap, p);

    is_reachable[n] = 1;
  }

  // Now do the transitive closure of the reachability relation.
  node_t i, j;

  assert(heap->nnodes <= NABSNODES);

  for (i = 1; i < heap->nnodes && i < NABSNODES; i++) {
    for (j = 1; j < heap->nnodes && j < NABSNODES; j++) {
      if (is_reachable[j]) {
        n = next(heap, j);
        is_reachable[n] = 1;
      }
    }
  }

  // Now copy all of the reachable nodes into the next generation.
  word_t nreachable = 0;

  for (n = 0; n < heap->nnodes && n < NABSNODES; n++) {
    if (is_reachable[n]) {
      reachable_nodes[nreachable] = n;
      nreachable++;
    }
  }

  return nreachable;
}

/*
 * Reclaim any nodes that are no longer reachable.
 */
static void destructive_gc(abstract_heapt *heap) {
  word_t nreachable;
  node_t reachable_nodes[NABSNODES];

  nreachable = find_reachable(heap, reachable_nodes);

  // Don't bother moving null
  word_t ncopied = 1;
  word_t k;
  node_t n;

  for (k = 1; k < nreachable && k < NABSNODES; k++) {
    n = reachable_nodes[k];
    destructive_move_node(heap, n, ncopied);
    ncopied++;
  }

  heap->nnodes = ncopied;
}

/*
 * x = n;
 *
 * x is a pointer, n is a graph node.
 */
static void destructive_assign_ptr(abstract_heapt *heap,
                                   ptr_t x,
                                   node_t n) {
  assert(x < NPROG);
  assert(n < heap->nnodes);

  word_t px = heap->ptr[x];
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
  assert(x < heap->nnodes);
  assert(y < heap->nnodes);

  node_t xn = next(heap, x);

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
  assert(x < NPROG);
  assert(y < NPROG);

  copy_abstract(pre, post);

  node_t py = deref(post, y);
  destructive_assign_ptr(post, x, py);

  destructive_gc(post);
}

/*
 * Allocate a new node.
 */

static node_t destructive_alloc(abstract_heapt *heap) {
  assert(heap->nnodes < NABSNODES);

  return heap->nnodes++;
}

/*
 * x = new();
 */
void abstract_new(abstract_heapt *pre,
                  abstract_heapt *post,
                  ptr_t x) {
  assert(x < NPROG);

  copy_abstract(pre, post);

  // Just allocate a new node and have x point to it.
  node_t n = destructive_alloc(post);
  destructive_assign_next(post, n, null_node, 1);
  destructive_assign_ptr(post, x, n);

  destructive_gc(post);
}

/*
 * x = y->n
 */
void abstract_lookup(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  assert(x < NPROG);
  assert(y < NPROG);

  node_t py = deref(pre, y);
  node_t yn = next(pre, py);

  word_t y_yn_dist = dist(pre, py);

  __CPROVER_assume(py != null_node);

  assert(y_yn_dist > 0);

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
    destructive_gc(post);
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

    destructive_gc(post);
  }
}

/*
 * x->n = y;
 */
void abstract_update(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  assert(x < NPROG);
  assert(y < NPROG);

  copy_abstract(pre, post);

  node_t px = deref(post, x);
  node_t xn = next(post, x);

  node_t py = deref(post, y);

  destructive_assign_next(post, px, py, 1);
  destructive_gc(post);
}

/*
 * Check that the heap is well formed.
 */
int valid_abstract_heap(abstract_heapt *heap) {
  // There is at least one node (null)
  if (heap->nnodes <= 0) {
    return 0;
  }

  // There are not too many nodes.
  if (heap->nnodes > NABSNODES) {
    return 0;
  }

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

  for (n = 0; n < heap->nnodes && n < NABSNODES; n++) {
    if (next(heap, n) >= heap->nnodes) {
      return 0;
    }
  }

  // Each node, except null, is > 0 away from its successor.
  for (n = 0; n < heap->nnodes && n < NABSNODES; n++) {
    if (n != null_node && dist(heap, n) <= 0) {
      return 0;
    }

    if (dist(heap, n) >= INF) {
      return 0;
    }
  }

  return is_minimal(heap);
}

/*
 * Compute the heap facts, i.e. all the pairwise distances between program
 * variables.
 */
void consequences(abstract_heapt *heap,
                  heap_factst *facts) {
  word_t min_dists[NABSNODES];
  ptr_t x, y;
  node_t n;
  word_t curr_dist;
  word_t i;

  for (x = 0; x < NPROG; x++) {
    memset(min_dists, INF, sizeof(min_dists));
    n = deref(heap, x);
    curr_dist = 0;
    min_dists[n] = 0;

    // First compute the distance form x to each heap node...
    for (i = 0; i < NABSNODES; i++) {
      curr_dist += dist(heap, n);
      n = next(heap, n);

      if (min_dists[n] != INF) {
        // We've hit a cycle.
        break;
      }

      min_dists[n] = curr_dist;
    }

    // Now fill in the heap facts!
    for (y = 0; y < NPROG; y++) {
      n = deref(heap, y);
      facts->dists[x][y] = min_dists[n];
    }
  }
}

/*
 * Create an initial heap where everything points to null.
 */
void init_abstract_heap(abstract_heapt *heap) {
  heap->nnodes = 1;

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
  word_t reachable_nodes[NABSNODES];
  word_t nreachable;

  nreachable = find_reachable(heap, reachable_nodes);

  // Find the indegree of each node, restricted to just the reachable subgraph.
  word_t indegree[NABSNODES];
  memset(indegree, 0, sizeof(indegree));

  word_t i;

  for (i = 0; i < nreachable && i < NABSNODES; i++) {
    n = reachable_nodes[i];
    m = next(heap, n);
    indegree[m]++;
  }

  // Check there are no unnamed nodes with indegree <= 1.
  for (n = 0; n < heap->nnodes && n < NABSNODES; n++) {
    if (!is_named[n] && indegree[n] <= 1) {
      return 0;
    }
  }

  return 1;
}
