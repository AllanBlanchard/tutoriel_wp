int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 29;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 29){
    i++ ;
  }

  if(i < 30){
    ++i;
    
    if(i == 30){
      i = 42 ;
      h = 84 ;
    }
  }
  //@assert i == 42;
  //@assert h == 84;
}
