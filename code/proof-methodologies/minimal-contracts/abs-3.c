/*@ 
  requires x > INT_MIN ;
*/
int abs(int x){
  return (x < 0) ? -x : x ;
}
