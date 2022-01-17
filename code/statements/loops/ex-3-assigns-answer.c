/* run.config
   OPT:-wp -wp-par 1 -wp-cache update -wp-cache-env -wp-msg-key shell
*/

void foo(){
  int h = 42 ;
  int x = 0 ;
  int e = 0 ;
  /*@ loop assigns e, x ; */
  while(e < 10){
    ++ e ;
    x += e * 2 ;
  }
  //@ assert h == 42 ;
}


void bar(){
  int h = 42 ;
  int x = 0 ;
  int e = 0 ;
 PreLoop:
  /*@ loop invariant h == \at(h, PreLoop) ; */
  while(e < 10){
    ++ e ;
    x += e * 2 ;
  }
  //@ assert h == 42 ;
}


/*
  We can deduce that the loop assigns clause is a particular class of
  loop invariant, exactly as assigns are a particula class of post-condition:
  any variable that is not mentioned in this list keeps its old value.
*/
