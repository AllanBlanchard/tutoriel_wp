void function(int a[5]){
  //@ ghost int even[5] = { 0 };
  //@ ghost int \ghost * pe = even ;

  for(int *p = a; p < a+5; ++p){
    //@ ghost if(*p % 2) *pe = 1;
    //@ ghost pe++;
  }
}
