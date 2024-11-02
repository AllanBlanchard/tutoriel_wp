/* run.config
   OPT: -wp -wp-print -wp-no-let -wp-prover qed -wp-prop="C3,I4" -wp-msg-key shell
*/

int main(void) {
  int x = 0, y = 0 ;

  /*@       loop invariant I1: 0 <= x ;
      admit loop invariant A2: x <= 10 ;
      check loop invariant C3: y <= 20 ;
            loop invariant I4: y == 2 * x ;
      loop assigns x ;
  */
  while (x < 10) {
    x++ ;
    y += 2 ;
  }
}
