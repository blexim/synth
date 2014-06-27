#ifndef IO_H
#define IO_H

#include "synth.h"

extern unsigned int **test_vectors;
extern int numtests;

void load_tests();
void free_tests();

void load_solution(solution_t *solution);

#endif
