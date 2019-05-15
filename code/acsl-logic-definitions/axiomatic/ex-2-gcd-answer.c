#include <limits.h>

/*@ 
  axiomatic GCD {
    logic integer gcd(integer a, integer b) reads \nothing ;

    axiom gcd_zero: \forall integer n; n == gcd(n, 0);
    axiom gcd_succ: \forall integer a, b ; gcd(b, a % b) == gcd(a, b);
  }
*/

/*@
  requires a >= 0 && b >= 0 ;
  assigns \nothing ;
  ensures \result == gcd(a, b) ;
*/
int gcd(int a, int b){
  /*@
    loop invariant a >= 0 && b >= 0 ;
    loop invariant gcd(a, b) == gcd(\at(a, Pre), \at(b, Pre)) ;
    loop assigns a, b ;
    loop variant b ;
  */ 
  while (b != 0){
    int t = b;
    b = a % b;
    a = t;
  }
  return a;
}
