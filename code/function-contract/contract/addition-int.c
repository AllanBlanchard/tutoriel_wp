/* run.config
   STDOPT:+"-wp-no-rte"
*/

//@ ensures \result == x + y ;
int add(int x, int y){
  return x+y ;
}
