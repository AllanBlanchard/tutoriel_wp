/* run.config
   OPT:
*/

int leap(int y){
  return ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ;
}

int days_of(int m, int y){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  int n = days[m-1] ;
  // code
}
