/* run.config
   STDOPT:+"-wp-smoke-tests"
*/

#include <limits.h>

/*@
  axiomatic Factorial{
    logic int factorial(integer n);

    axiom factorial_0:
      \forall integer i; i <= 0 ==> 1 == factorial(i) ;

    axiom factorial_n:
      \forall integer i; i > 0 ==> i * factorial(i-1) == factorial(i) ;
  }
*/

// We help solvers figuring out that there is a problem
//@ lemma fact_12: factorial(12) == 479001600;
//@ lemma fact_13: factorial(13) == 6227020800;

//@ requires factorial(x) == 1;
void example(int x) {}
