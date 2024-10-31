/* run.config
   OPT:
*/

int sum_n(int n){
  if(n < 1) return 0 ;

  int res = 0 ;
  for(int i = 1 ; i <= n ; i++){
    res += i ;
  }
  return res ;
}
