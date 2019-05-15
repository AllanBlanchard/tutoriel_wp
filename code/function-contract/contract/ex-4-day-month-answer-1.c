/*@
  requires 1 <= m <= 12 ;
  ensures m == 2 ==> \result == 28 ;
  ensures (m == 1 || m == 3 || m == 5 || m == 7 || m == 8 || m == 10 || m == 12) ==> \result == 31 ;
  ensures (m == 4 || m == 6 || m == 9 || m == 11) ==> \result == 30 ;
*/
int day_of(int m){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  return days[m-1] ;
}
