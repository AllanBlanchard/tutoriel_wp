/* run.config
   EXIT: 1
   STDOPT:
*/

int sum(int n){
  int x = 0 ;
  for(int i = 0; i <= n; ++i){
    //@ ghost break;
    x += i ;
  }
  return x;
}
