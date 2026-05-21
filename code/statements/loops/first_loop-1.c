/* run.config
   STDOPT:
   OPT: -wp -wp-par 1 -wp-prover none -wp-no-subst -wp-print
*/

int main(){
  int i = 0;

  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@ assert i == 30;
}
