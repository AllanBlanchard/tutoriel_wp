/*@
  inductive is_fibo{L}(integer n, integer r){
  case fib_0: is_fibo(0, 1) ;
  case fib_1: is_fibo(1, 1) ;
  case fib_N: 
    \forall integer n, p_1, p_2, r ;
    n > 1 ==> is_fibo(n-2, p_2) ==> is_fibo(n-1, p_1) ==> is_fibo(n, p_2+p_1) ;
  }
*/

/*@
  requires n > 1 && is_fibo(n-2, p_2) && is_fibo(n-1, p_1) ;
  assigns \nothing ;
  ensures is_fibo(n, p_2+p_1) ;
*/
void helper(int n, int p_1, int p_2){}

/*@
  requires n >= 0 ;
  assigns  \nothing ;
  ensures  is_fibo(n, \result);
*/
int fibo(int n){
  if(n < 2) return 1 ;

  int p_1 = 1 ;
  int r = p_1 + 1 ;

  // @ ghost helper(2, p_1, 1);

  /*@
    loop invariant 2 <= i <= n ;
    loop invariant is_fibo(i-1, p_1) ;
    loop invariant is_fibo(i, r) ;
    loop assigns i, p_1, r ;
    loop variant n - i ;
  */
  for(int i = 2 ; i < n ; ++i){
    int x = r + p_1 ;
    // @ ghost helper(i+1, r, p_1);
    p_1 = r ;
    r = x ;
  }
  return r ;
}
