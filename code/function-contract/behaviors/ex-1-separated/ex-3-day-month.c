/*@
  requires 1 <= m <= 12 ;
  ensures m \in { 2 } ==> \result == 28 ;
  ensures m \in { 1, 3, 5, 7, 8, 10, 12 } ==> \result == 31 ;
  ensures m \in { 4, 6, 9, 11 } ==> \result == 30 ;
*/
int day_of(int m){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  return days[m-1] ;
}
