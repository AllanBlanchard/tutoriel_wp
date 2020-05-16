int sum(int n){
  int x = 0 ;
  for(int i = 0; i <= n; ++i){
    //@ ghost if(i > n) break;
    x += i ;
  }
  return x;
}
