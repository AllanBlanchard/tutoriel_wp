/*@
  requires 0 <= first <= 180 ;
  requires 0 <= second <= 180 ;
  requires first + second <= 180 ;

  ensures 180 == first + second + \result ;
  ensures 0 <= \result <= 180 ;
*/
int last_angle(int first, int second){
  return 180 - first - second ;
}
