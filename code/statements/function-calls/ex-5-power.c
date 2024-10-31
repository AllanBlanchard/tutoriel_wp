/* run.config
   OPT:
*/

/*@
  requires \true ; // to complete
  terminates \true ; // to complete
  decreases 0 ; // to complete
*/
int rec_power(int x, int n){
  if(n == 0) return 1 ;
  else if(n % 2 == 0) return rec_power(x * x, n / 2) ;
  else return x * rec_power(x, n - 1) ;
}
