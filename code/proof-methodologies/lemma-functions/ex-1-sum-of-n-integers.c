/*@
  logic integer sum_of_n_integers(integer n) =
    (n <= 0) ? 0 : sum_of_n_integers(n-1) + n ;
*/

/*@
  assigns \nothing ;
  ensures ... ;
*/
void lemma_value_of_sum_of_n_integers_2(unsigned n){
  // ...
}

/*@
  logic integer sum_of_range_of_integers(integer fst, integer lst) =
    ((lst <= fst) ? lst : lst + sum_of_range_of_integers(fst, lst-1)) ;
*/

/*@
  requires fst <= lst ;
  assigns \nothing ;
  ensures ((lst-fst+1)*(fst+lst))/2 == sum_of_range_of_integers(fst, lst) ;
*/
void lemma_value_of_sum_of_range_of_integers(int fst, int lst){
  // ...
}

/*@
  requires n*(n+1) <= UINT_MAX ;
  assigns \nothing ;
  ensures \result == sum_of_n_integers(n);
*/
unsigned sum_n(unsigned n){
  return (n*(n+1))/2 ;
}
