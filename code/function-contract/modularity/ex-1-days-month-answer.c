/*@ 
  assigns \nothing ;
  ensures \result <==> ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0);
*/
int leap(int y){
  return ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ;
}

/*@
  requires 1 <= m <= 12 ;

  assigns \nothing ;

  behavior february_leap:
    assumes m \in { 2 } ;
    assumes ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ;
    ensures \result == 29 ;

  behavior february_not_leap:
    assumes m \in { 2 } ;
    assumes ! ( ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ) ;
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
int day_of(int m, int y){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  int n = days[m-1] ;
  if(n == 28){
    if(leap(y)) return 29 ;
    else return 28 ;
  }
  return n ;
}
