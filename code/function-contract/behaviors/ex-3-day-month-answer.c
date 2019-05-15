/*@
  requires 1 <= m <= 12 ;

  assigns \nothing ;

  behavior february:
    assumes m \in { 2 } ;
    ensures \result == 28 ;

  behavior thirty:
    assumes m \in { 4, 6, 9, 11 } ;
    ensures \result == 30 ;

  behavior thirty_one:
    assumes m \in { 1, 3, 5, 7, 8, 10, 12 } ;
    ensures \result == 31 ;

  complete behaviors;
  disjoint behaviors;
*/
int day_of(int m){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  return days[m-1] ;
}
