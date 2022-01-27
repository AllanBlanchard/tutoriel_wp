/* run.config
   OPT:
*/

/*@
  inductive is_power(integer x, integer n, integer r) {
  case zero: \true; // to complete
  case N: \true; // to complete
  }
*/

/*@
  lemma power_even: \true; // to complete
  lemma power_odd: \true; // to complete
*/

/*@
  requires n >= 0 ;
  // assigns ...
  // ensures ...
*/
int power(int x, int n){
  int r = 1 ;
  /*@
    loop invariant 1 <= i <= n+1 ;
    // loop invariant ...
  */
  for(int i = 1 ; i <= n ; ++i){
    r *= x ;
  }
  return r ;
}

/*@
  requires n >= 0 ;
  // assigns ...
  // ensures ...
*/
int fast_power(int x, int n){
  int r = 1 ;
  int p = x ;
  /*@
    loop invariant \forall integer v ; \true; // to complete
  */
  while(n > 0){
    if(n % 2 == 1) r = r * p ;
    p *= p ;
    n /= 2 ;
  }
  //@ assert is_power(p, n, 1) ;

  return r ;
}
