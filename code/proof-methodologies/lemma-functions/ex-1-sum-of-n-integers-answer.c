#include <limits.h>

/*@
  logic integer sum_of_n_integers(integer n) =
    (n <= 0) ? 0 : sum_of_n_integers(n-1) + n ;
*/

/*@ ghost
  /@
    assigns \nothing ;
    ensures (n*(n+1)) / 2 == sum_of_n_integers(n) ;
  @/
  void lemma_value_of_sum_of_n_integers_2(unsigned n){
    /@
      loop invariant 0 <= i <= n ;
      loop invariant (i*(i+1)) == 2 * sum_of_n_integers(i) ;
      loop assigns i ;
      loop variant n - i ;
    @/
    for(unsigned i = 0 ; i < n ; ++i);
  }
*/

/*@
  logic integer sum_of_range_of_integers(integer fst, integer lst) =
    ((lst <= fst) ? lst : lst + sum_of_range_of_integers(fst, lst-1)) ;
*/

/*@ ghost
  /@
    requires fst <= lst ;
    assigns \nothing ;
    ensures ((lst-fst+1)*(fst+lst))/2 == sum_of_range_of_integers(fst, lst) ;
  @/
  void lemma_value_of_sum_of_range_of_integers(int fst, int lst){
    /@
      loop invariant fst <= i <= lst ;
      loop invariant (i-fst+1)*(fst+i) == 2 * sum_of_range_of_integers(fst, i) ;
      loop assigns i ;
      loop variant lst - i ;
    @/
    for(int i = fst ; i < lst ; ++i);
  }
*/

/*@
  requires n*(n+1) <= UINT_MAX ;
  assigns \nothing ;
  ensures \result == sum_of_n_integers(n);
*/
unsigned sum_n(unsigned n){
  //@ ghost lemma_value_of_sum_of_n_integers_2(n);
  //@ assert n * (n+1) >= 0 ; // necessary in Scandium
  return (n*(n+1))/2 ;
}
