#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFERSIZE 200
#define TRUE 1
#define FALSE 0

typedef struct state {
  //char input[BUFFERSIZE+50];
  //char localbuf[BUFFERSIZE];
  char nc;
  char c;
  unsigned int p;
  unsigned int upperlimit;
  unsigned int quotation;
  unsigned int roundquote;
  unsigned int idx;
} state_t;

