/* run.config
   OPT:-wp -wp-par 1 -wp-cache update -wp-cache-env -wp-msg-key shell
*/

void foo(){
  int x = -20 ;

  /*@
    loop variant -x ;
  */
  while(x < 0){
    x += 4 ;
  }
}

void bar(){
  int x = -20 ;
  int i = 5 ;

  /*@
    loop invariant (-i) * 4 == x ;
    loop variant i ;
  */
  while(x < 0){
    x += 4 ;
    i -- ;
  }
}
