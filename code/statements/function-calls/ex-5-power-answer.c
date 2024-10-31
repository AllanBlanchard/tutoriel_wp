/* run.config
   STDOPT:+"-wp-no-rte"
*/

/*@
  requires n >= 0 ;
  terminates \true ;
  decreases n ;
*/
int rec_power(int x, int n){
  if(n == 0) return 1 ;
  else if(n % 2 == 0) return rec_power(x * x, n / 2) ;
  else return x * rec_power(x, n - 1) ;
}
