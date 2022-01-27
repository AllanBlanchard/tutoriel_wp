/* run.config
   STDOPT:+"-wp-prover alt-ergo,coq -wp-session @PTEST_SUITE_DIR@/oracle@PTEST_CONFIG@/@PTEST_NAME@.session"
*/

#include <limits.h>

/*@
  inductive is_sum_n(integer n, integer res) {
  case nul:     \forall integer n ; n <= 0 ==> is_sum_n(n, 0) ;
  case not_nul: \forall integer n, p ; n > 0 ==> is_sum_n(n-1, p) ==> is_sum_n(n, n+p) ;
  }
*/

/*@
  lemma sum_n_value:
    \forall integer n, r ;
      n >= 0 ==> is_sum_n(n, r) ==> 2 * r == (n*(n+1)) ;
*/
/*@
  lemma sum_n_value_direct:
    \forall integer n, r ;
      n >= 0 ==> is_sum_n(n, r) ==> r == (n*(n+1))/2 ;
*/


/*@
  requires n*(n+1) <= 2*INT_MAX ;
  assigns \nothing ;
  ensures is_sum_n(n, \result) ;
*/
int sum_n(int n){
  if(n < 1) return 0 ;

  int res = 0 ;
  /*@
    loop invariant 1 <= i <= n+1 ;
    loop invariant is_sum_n(i-1, res) ;
    loop assigns i, res ;
    loop variant n - i ;
  */
  for(int i = 1 ; i <= n ; i++){
    res += i ;
  }
  return res ;
}
