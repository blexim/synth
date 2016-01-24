/* Initial program:
  extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

extern unsigned int __VERIFIER_nondet_uint();
extern _Bool __VERIFIER_nondet_bool();

int main()
{
  unsigned int x1=__VERIFIER_nondet_uint(), x2=__VERIFIER_nondet_uint(), x3=__VERIFIER_nondet_uint();
  unsigned int d1=1, d2=1, d3=1;
  _Bool c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();
  
  while(x1>0 && x2>0 && x3>0)
  {
    if (c1) x1=x1-d1;
    else if (c2) x2=x2-d2;
    else x3=x3-d3;
    c1=__VERIFIER_nondet_bool();
    c2=__VERIFIER_nondet_bool();
  }

  __VERIFIER_assert(x1==0 && x2==0 && x3==0);
  return 0;
}
*/

  int inv(unsigned int x1, unsigned int x2, unsigned int x3) {
    return (x1>0 || x2>0 || x3>0);
  }

int main()
{
  unsigned int x1=nondet(), x2=nondet(), x3=nondet();
  unsigned int d1=1, d2=1, d3=1;
  int c1=nondet(), c2=nondet();
  

  /*
  while(x1>0 && x2>0 && x3>0)
  {
    if (c1) x1=x1-d1;
    else if (c2) x2=x2-d2;
    else x3=x3-d3;
    c1=nondet();
    c2=nondet();
  }
  */


    // prove inductiveness
    /* x1 = nondet(); */
    /* x2 = nondet(); */
    /* x3 = nondet(); */
    /* c1 = nondet(); */
    /* c2 = nondet(); */
  
    /* __CPROVER_assume(inv(x1,x2,x3) && (x1>0 && x2>0 && x3>0)); */

    /* if (c1) x1=x1-d1; */
    /* else if (c2) x2=x2-d2; */
    /* else x3=x3-d3; */
    /* c1=nondet(); */
    /* c2=nondet(); */

    /* assert(inv(x1,x2,x3)); */

  
    // get initial state
    x1 = nondet();
    x2 = nondet();
    x3 = nondet();
    __CPROVER_assume(inv(x1,x2,x3) && !(x1>0 && x2>0 && x3>0));

    assert(x1==0 && x2==0 && x3==0);



  return 0;
}
