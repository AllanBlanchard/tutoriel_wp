/* run.config
   EXIT: 1
   STDOPT:
*/

int sum(int n){
  int x = 0 ;
  for(int i = 0; i <= n; ++i){
    x += i ;
    //@ ghost x++;
  }
  return x;
}
