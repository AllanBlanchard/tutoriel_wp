//@ ghost int x ;

/*@ ghost
  /@ assigns x ; @/
  void ghost_foo(void);
*/

/*@ assigns x ; */
void foo(void){
  /*@ ghost
    /@ loop assigns x ; @/
    for(int i = 0; i < 10; ++i);
  */
}
