/*@ 
  requires x > INT_MIN ;
  assigns  \nothing ;
  ensures  \result >= 0 ;
*/
int abs(int x){
  return (x < 0) ? -x : x ;
}
