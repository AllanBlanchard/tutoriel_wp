/* run.config
   STDOPT:+"-wp-no-rte"
*/

/*@
  ensures \result >= 0;
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
