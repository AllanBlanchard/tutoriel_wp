/*@
  requires 0 <= first <= 180 ;
  requires 0 <= second <= 180 ;
  ensures 180 == first + second + \result ;
*/
int last_angle(int first, int second){
  return 180 - first - second ;
}
