void foo(){
  int i ;
  int x = 0 ;
  /*@
    loop invariant 0 <= i <= 19 ;
    loop assigns i ;
    loop variant 20 - i ;
  */
  for(i = 0 ; i < 20 ; ++i){
    if(i == 19){
      x++ ;
      break ;
    }
  }
  //@ assert x == 1 ;
  //@ assert i == 19 ;
}
