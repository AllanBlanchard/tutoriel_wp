int x ;

/*@ ghost
  /@ assigns x ; @/
  void ghost_foo(void);
*/

void foo(void){
  /*@ ghost
    /@ assigns x ; @/
    for(int i = 0; i < 10; ++i);
  */
}
