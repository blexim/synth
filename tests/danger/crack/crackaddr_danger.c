/*
  Copyright (c) 2011, Thomas Dullien
  All rights reserved.

  Redistribution and use in source and binary forms, with or without 
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright notice,
  this list of conditions and the following disclaimer. Redistributions 
  in binary form must reproduce the above copyright notice, this list of
  conditions in the documentation and/or other materials provided with 
  the distribution.
  
  **********************************************************************
  
  Static analysis challenge: Dealing with the implicit state machine
  
  These two files (simple_example_good.c, simple_example_bad.c) are 
  designed to illustrate a particular shortcoming of code analysis tools
  as they exist today: The neglect of the existence of implicit state
  machines and their effect.
  
  The code is loosely inspired by the crackaddr() overflow that Mark
  Dowd found in Sendmail in March 2003. It is also related to the 
  prescan()-bugs that Michal Zalewski found in the same year.
  
  The code contains an implicit state machine with the following 
  states:
  
    1. quotation = roundquote = false
    2. quotation = true, roundquote = false
    3. quotation = false, roundquote = true
    4. quotation = true, roundquote = true
    
  The following transitions are possible (hope I didn't miss any):
    1->2, 1->3, 2->1, 3->1, 3->4, 4->3
  
  The "bad" variant of this file contains the problem that the trans-
  ition 1->3 fails to decrement "upperlimit". An attacker can, by repeat-
  edly cycling through this state transition (for example by issuing an 
  input string of "()()()()...", move the upperlimit variable to point
  behind the end of localbuf. In order to reach this state, at least 10
  iterations are required, though.
  
  This code is difficult to analyze automatically for the following 
  reasons:
  
  1) The behavior of the loop is dependent on previous iterations, and
  in a way that leads to overapproximation in most abstract inter-
  pretation frameworks. This overapproximation (due to not really taking
  into account the implicit state machine) makes it difficult to tell 
  the "good" case from the "bad" case.
  
  2) The loop body itself has at least 8 different paths that can be
  taken on each iteration ('<', '>', '(', ')', upperlimit reached or
  not). In order to get to an invalid state, at least 9 iterations of
  the loop are required. A (completely incorrect, but nonetheless 
  insight-generating) calculation gets us to 2^3^9 = 2^27 states,
  sufficient to thwart a naive "let's explore all possible paths" 
  approach. 
  
  Long story short: I believe that these two files summarize well some
  of the reasons why code analysis tools are not very good at finding
  sophisticated bugs with a very low false positive rate. If you have
  any automated code analysis that detects the issue in the bad example
  and does not detect the issue in the good example, I'd be excited to
  hear from you :-) thomas.dullien@zynamics.com

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFERSIZE 20
#define TRUE 1
#define FALSE 0

char input[BUFFERSIZE+50];
char localbuf[ BUFFERSIZE ];
char c;
int src, dst;
int upperlimit;
int quotation;
int roundquote;

int guard() {
  return c != '\0';
}

int strong_guard() {
  return input[src] == 40 && input[src+1] == 41 &&
    upperlimit < BUFFERSIZE;
}


int body() {
    if(( c == '<' ) && (!quotation)) {
      quotation = TRUE;
      upperlimit--;}
    if(( c == '>' ) && (quotation)){
      quotation = FALSE;
      upperlimit++;}
    if(( c == '(' ) && ( !quotation ) && !roundquote){
      roundquote = TRUE;
      /*upperlimit--;*/}
    if(( c == ')' ) && ( !quotation ) && roundquote){
      roundquote = FALSE;
      upperlimit++;}
    // If there is sufficient space in the buffer, write the character.
    if( dst < upperlimit ) {
      assert(dst < BUFFERSIZE);
      localbuf[dst++] = c;
    }

  c = input[src++];
}

int copy_it()
{
  while (guard()) {
    body();
  }
}

int in_range(int x) {
  return x >= 0 && x < BUFFERSIZE;
}
 
int main() {
  char nondet_input[ BUFFERSIZE+50 ];
  int prefix = nondet();
  int i;

  c = nondet();
  src = nondet();
  dst = nondet();
  upperlimit = nondet();
  quotation = nondet();
  roundquote = nondet();
  //memset( localbuf, 0, BUFFERSIZE );

  memcpy(input, nondet_input, sizeof(input));

  //c = input[src];

  /*
  while (guard() && strong_guard()) {
    body();
    body();
  }
  */

  //upperlimit = nondet();
  //__CPROVER_assume(upperlimit > BUFFERSIZE && upperlimit <= BUFFERSIZE+10);
  //quotation = nondet();
  //roundquote = nondet();

  __CPROVER_assume(upperlimit >= BUFFERSIZE);
  if (guard()) {
    body();
  }
  //copy_it();

  //assert(upperlimit > initial_upperlimit);
}
