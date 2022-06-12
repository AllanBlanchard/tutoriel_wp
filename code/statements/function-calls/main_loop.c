int debug_steps = -1 ;

/*@ requires debug_steps >= -1 ;
    terminates debug_steps > 0 ;
 */
void main_loop(void){
  /*@ loop invariant debug_steps == -1
                  || 0 <= debug_steps <= \at(debug_steps, Pre) ;
      loop assigns debug_steps ;
      loop variant debug_steps ; */
  while(1){
    if(debug_steps == 0) return ;
    else debug_steps -- ;

    // actual code
  }
}
