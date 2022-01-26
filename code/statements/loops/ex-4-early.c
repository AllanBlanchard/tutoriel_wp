/* run.config
   OPT:
*/

void foo(){
  int i ;
  int x = 0 ;
  for(i = 0 ; i < 20 ; ++i){
    if(i == 19){
      x++ ;
      break ;
    }
  }
  //@ assert x == 1 ;
  //@ assert i == 19 ;
}
