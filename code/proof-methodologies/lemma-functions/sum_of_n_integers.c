/*@
  logic integer sum_of_n_integers(integer n) =
    (n <= 0) ? 0 : sum_of_n_integers(n-1) + n ;
*/

/*@
  requires n <= 92681 ;
  assigns \nothing ;
  ensures (n*(n+1)) / 2 == sum_of_n_integers(n) ;
*/
void lemma_value_of_sum_of_n_integers(unsigned n){
  unsigned result = 0 ;

  /*@
    loop invariant 0 <= i <= n ;
    loop invariant result == (i*(i+1)) / 2 ;
    loop invariant result == sum_of_n_integers(i) ;
    loop assigns result, i ;
    loop variant n - i ;
  */
  for(unsigned i = 0 ; i < n ; ++i){
    result += (i+1) ;
  }
}
  
/*@
  assigns \nothing ;
  ensures (n*(n+1)) / 2 == sum_of_n_integers(n) ;
*/
void lemma_value_of_sum_of_n_integers_2(unsigned n){
  /*@
    loop invariant 0 <= i <= n ;
    loop invariant (i*(i+1)) / 2 == sum_of_n_integers(i) ;
    loop assigns i ;
    loop variant n - i ;
  */
  for(unsigned i = 0 ; i < n ; ++i);
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
  /*@
    loop invariant fst <= i <= lst ;
    loop invariant (i-fst+1)*(fst+i) == 2 * sum_of_range_of_integers(fst, i) ;
    loop assigns i ;
    loop variant lst - i ;
  */
  for(int i = fst ; i < lst ; ++i);
}
