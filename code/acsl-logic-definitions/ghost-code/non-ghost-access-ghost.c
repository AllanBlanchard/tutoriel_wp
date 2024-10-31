/* run.config
   EXIT: 1
   STDOPT:
*/

int sum_42(int n){
  int x = 0 ;
  //@ ghost int r = 42 ;
  for(int i = 0; i < n; ++i){
    x += r;
  }
  return x;
}
