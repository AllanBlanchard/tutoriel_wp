#include <limits.h>

/*@
  logic integer square(integer n) = n*n ;
*/

/*@
  requires INT_MIN < x;

  assigns \nothing ;

  ensures x >= 0 ==> \result == x ; 
  ensures x < 0 ==> \result == -x ;
*/
int abs(int x){
  return (x < 0) ? -x : x ;
}

/*@
  requires x*x <= UINT_MAX ;
  assigns \nothing ;
  ensures \result == square(x) ;
*/
unsigned square(int x){
  unsigned v = abs(x) ;
  return v * v ;
}
