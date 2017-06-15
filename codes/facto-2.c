#include <limits.h>

/*@
  logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);

  lemma growing_facto:
    \forall integer n, m ; 0 <= n < m ==> factorial(n) <= factorial(m);
*/

/*@
  requires n * factorial(n-1) <= UINT_MAX;
   ensures \result == factorial(n) ;
*/
unsigned facto(unsigned n){
  if(n == 0)
    return 1;
  else{
    /*@ assert 0 <= n-1 < n ==> factorial(n-1) <= factorial(n); */
    /*@ assert factorial(n) == n * factorial(n-1) ; */
    /*@ assert factorial(n-1) <= factorial(n); */
    /*@ assert factorial(n-1) == (n-1)*factorial(n-1-1) || factorial(n-1) == 1; */
    return n * facto(n-1);
  }
}

int main(){
  unsigned a0  = facto(0);
  unsigned a1  = facto(1);
  unsigned a2  = facto(2);
  unsigned a3  = facto(3);
  unsigned a4  = facto(4);
  unsigned a5  = facto(5);
  unsigned a6  = facto(6);
  unsigned a7  = facto(7);
  unsigned a8  = facto(8);
  unsigned a9  = facto(9);
  unsigned a10 = facto(10);
  unsigned a11 = facto(11);
  unsigned a12 = facto(12);
}
