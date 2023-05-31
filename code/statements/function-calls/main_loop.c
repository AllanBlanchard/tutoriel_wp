/* run.config
   STDOPT:
   STDOPT:+"-wp-variant-with-terminates"
*/

int debug_steps = -1 ;

/*@ requires debug_steps >= -1 ;
    terminates debug_steps >= 0 ;
 */
void main_loop(void){
  /*@ loop invariant \at(debug_steps, Pre) == -1
                  || 0 <= debug_steps <= \at(debug_steps, Pre) ;
      loop assigns debug_steps ;
      loop variant debug_steps ; */
  while(1){
    if(debug_steps == 0) return ;
    else if(debug_steps > 0) debug_steps -- ;

    // actual code
  }
}
