int main(){
  int i = 0;
  
  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
}
