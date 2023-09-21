/* run.config
   OPT: -wp -wp-print -wp-no-let -wp-prover qed
*/

int main(void){
  int x = 0 ;

  /*@ loop invariant I1: 0 <= x ;
      loop invariant I2: x <= 10 ;
      loop assigns x ;
  */
  while(x < 10) x++ ;
}
