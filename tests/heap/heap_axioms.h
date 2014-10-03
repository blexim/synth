#include "heapabstract.h"

int alias_axioms(abstract_heapt *heap);
int path_axioms(abstract_heapt *heap);
int null_axioms(abstract_heapt *heap);
int cycle_axioms(abstract_heapt *heap);

int acyclic(abstract_heapt *heap);
int no_sharing(abstract_heapt *heap);
