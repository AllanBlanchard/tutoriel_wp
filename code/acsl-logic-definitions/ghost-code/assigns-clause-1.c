/* run.config
   EXIT: 1
   STDOPT:
*/

int x ;

/*@ ghost
  /@ assigns x ; @/
  void ghost_foo(void);
*/

void foo(void){
  /*@ ghost
    /@ loop assigns x ; @/
    for(int i = 0; i < 10; ++i);
  */
}
