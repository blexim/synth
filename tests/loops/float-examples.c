/*
** termination-examples.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 08/05/13
**
** Some simple examples for looking at floating point termination.
** Inputs are assumed to be non-deterministic.
*/

#include <assert.h>
#include <math.h>

#ifdef EXECUTABLE
#define assume(A) if (!(A)) return 0
#else
#define assume(A) __CPROVER_assume(A)
#endif

// A simple feedback filter with an impulse input
// Termination depends on the rounding mode and (for RNE) the scaling
int feedback (float scaling) {
  float state;

  assume((0 < scaling) && (scaling < 1));

  state = 1;
  while (state > 0) {
    state *= scaling;
  }
 
  return 1;
}



// Variant using difference that should always terminate
int feedbackVariant (float scaling) {
  float state;
  float oldState;

  assume((0 < scaling) && (scaling < 1));

  oldState = 0;
  state = 1;
  while (fabs(state - oldState) > 0) {
    oldState = state;
    state *= scaling;
  }
 
  return 1;
}



// Heron's square root
// The time taken to terminate depends on the quality of the guess
// There are a few edge case in which a very bad guess will cause looping
// These mostly happen within a few iterations.
int heronsSqrt (float xsquared, float guess) {
  float state;
  float oldState;

  assume((0 < xsquared));
  assume((0 < guess));

  state = guess;
  oldState = 0;

  while (state != oldState) {
    oldState = state;
    state = (state + (xsquared / state)) / 2;
  }

  return 1;
}


// Variant in the more suitable form
int heronsSqrtVariant (float xsquared, float guess) {
  float state;
  float oldState;

  assume((0 < xsquared));
  assume((0 < guess));

  state = guess;
  oldState = 0;

  while (fabs(state - oldState) > 0) {
    oldState = state;
    state = (state + (xsquared / state)) / 2;
  }

  return 1;
}

// A subtle variant with different non-termination behaviour
int heronsSqrtBroken (float xsquared, float guess) {
  float state;
  float oldState;

  assume((0 < xsquared));
  assume((0 < guess));

  state = guess;
  oldState = 0;

  while (!(state == oldState)) {
    oldState = state;
    state = (state + (xsquared / state)) / 2;
  }

  return 1;
}



// Newton's method to find roots of a quadratic
// Looks simple but there are all kinds of edge cases.
// If the quadratic has no solutions then the algorithm will oscillate chaotically.
// The obvious condition *should* be sufficient to prevent this but ... well, that's the kind of thing we'd like to be able to prove.
// Conditions on the guess can be removed to give a couple of obvious edge cases
// Changing bracketing will also change things
int newtonQuadratic (float a, float b, float c, float guess) {
  float state;
  float oldState;

  assume(((b * b) - (4*(a*c))) > 0);
  assume((-0x1.fffffep+127f <= guess) && (guess <= 0x1.fffffep+127f));

  state = guess;

  do {
    oldState = state;
    state = state - (( (a*(state*state)) + ((b*state) + c) ) / 
		     ( (2*(a*state)) + b) );
  } while (state != oldState);

  return 1;
}

// Unlike the previous variant, this doesn't quite do the same thing
int newtonQuadraticVariant (float a, float b, float c, float guess) {
  float state;
  float oldState;

  assume(((b * b) - (4*(a*c))) > 0);
  assume((-0x1.fffffep+127f <= guess) && (guess <= 0x1.fffffep+127f));

  state = guess;

  do {
    oldState = state;
    state = state - (( (a*(state*state)) + ((b*state) + c) ) / 
		     ( (2*(a*state)) + b) );
  } while (fabs(state - oldState) > 0);

  return 1;
}

// and neither does this
int newtonQuadraticVariant2 (float a, float b, float c, float guess) {
  float state;
  float oldState;

  assume(((b * b) - (4*(a*c))) > 0);
  assume((-0x1.fffffep+127f <= guess) && (guess <= 0x1.fffffep+127f));

  state = guess;

  do {
    oldState = state;
    state = state - (( (a*(state*state)) + ((b*state) + c) ) / 
		     ( (2*(a*state)) + b) );
  } while (!(state == oldState));

  return 1;
}


// Simple example which does not terminate for reals but does for float
int halvingVariant1 (float x) {
  assume(x > 0);

  while (x > 0) {
    x = x * 0x1.fffffep-2f;  // The first floating-point number below 0.5
  }
}

// May terminate depending on rounding mode
int halvingVariant2 (float x) {
  assume(x > 0);

  while (x > 0) {
    x = x * 0.5;
  }
}

// Likewise
int halvingVariant3 (float x) {
  assume(x > 0);

  while (x > 0) {
    x = x * 0x1.000002p-1f;   // The first floating-point number above 0.5
  }

  return 1;
}


// Terminates for reals, may do for float depending on the relation between the numbers
int decrement (float start, float limit, float dec) {
  float state;

  assume(start > 0);
  assume(limit > 0);
  assume(dec > 0);

  state = start;

  if (state < limit) {
    while (state > 0) {
      state = state - dec;
    }
  }

  return 1;
}
