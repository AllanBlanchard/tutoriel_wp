/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0) ;
  case even_not_nul_natural{L}:
    \forall integer n ; n > 0 ==> even_natural(n-2) ==>
    // negative occurrence of even_natural
    !even_natural(n-1) ==> 
      even_natural(n) ;
  }
*/

/*@
  requires even_natural(n) ;
  ensures  \false ;
*/ void function(int n){

}
