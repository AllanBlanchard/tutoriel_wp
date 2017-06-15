#include <limits.h>

/*@
  logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);
*/

/*@
  requires n <= 12 ;
  assigns \nothing ;
  ensures \result == factorial(n) ;
*/
unsigned facto(unsigned n){
  /* @ assert \forall integer i, j ; i+1 == j ==> factorial(i) >= 1 ==> factorial(j) >= 1; */
  return (n == 0) ? 1 : n * facto(n-1);
}


int main(){
  unsigned v = facto(1);
}
