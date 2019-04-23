#include <limits.h>

/*@
  inductive is_sum_n(integer n, integer res) {
    // ...
  }
*/

/*@ 
  requires n*(n+1) <= 2*INT_MAX ;
  assigns \nothing ;
  // ensures ... ; 
*/
int sum_n(int n){
  if(n < 1) return 0 ;

  int res = 0 ;
  /*@
    loop invariant 1 <= i <= n+1 ;
    // loop invariant ... ; 
    loop assigns i, res ;
    loop variant n - i ;
  */
  for(int i = 1 ; i <= n ; i++){
    res += i ;
  }
  return res ;
}
