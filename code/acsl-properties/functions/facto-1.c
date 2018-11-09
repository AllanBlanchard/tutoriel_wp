/*@
  logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);
*/

/*@ 
  requires n <= 12 ;
  assigns \nothing ;
  ensures \result == factorial(n) ; 
*/
unsigned facto(unsigned n){
  return (n == 0) ? 1 : n * facto(n-1);
}
