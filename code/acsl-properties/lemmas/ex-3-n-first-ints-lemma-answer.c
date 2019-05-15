#include <limits.h>

/*@
  logic integer sum_n(integer n) = (n <= 0) ? 0 : n + sum_n(n-1);
*/
/*@
  lemma sum_n_value:
    \forall integer n ;
      n >= 0 ==> 2 * sum_n(n) == (n*(n+1)) ;
*/
/*@
  lemma sum_n_value_direct:
    \forall integer n ;
      n >= 0 ==> sum_n(n) == (n*(n+1))/2 ;
*/

/*@ 
  requires n*(n+1) <= 2*INT_MAX ;
  assigns \nothing ;
  ensures \result == sum_n(n) ; 
*/
int sum_n(int n){
  if(n < 1) return 0 ;

  int res = 0 ;
  /*@
    loop invariant 1 <= i <= n+1 ;
    loop invariant res == sum_n(i-1) ;
    loop assigns i, res ;
    loop variant n - i ;
  */
  for(int i = 1 ; i <= n ; i++){
    res += i ;
  }
  return res ;
}
