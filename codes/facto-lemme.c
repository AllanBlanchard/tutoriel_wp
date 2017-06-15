#include <limits.h>

/*@
  axiomatic Factorial{
    logic integer factorial(integer n);
    
    axiom factorial_0:
      \forall integer i; i <= 0 ==> 1 == factorial(i) ;

    axiom factorial_n:
      \forall integer i; i > 0 ==> i * factorial(i-1) == factorial(i) ;
  }
*/

/* @
  logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);
*/
/*@
  lemma factorial_gt_1_induction:
    \forall integer i, j ; i+1 == j ==> factorial(i) >= 1 ==> factorial(j) >= 1;
*/

/*@
  requires n * factorial(n-1) <= UINT_MAX;
  assigns \nothing ;
  ensures \result == factorial(n) ;
*/
unsigned facto(unsigned n){
  return (n == 0) ? 1 : n * facto(n-1);
}
