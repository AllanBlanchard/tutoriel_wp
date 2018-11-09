int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
