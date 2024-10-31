int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 30){
    //++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
