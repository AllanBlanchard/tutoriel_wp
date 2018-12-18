/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0);
  case even_not_nul_natural{L}:
    \forall integer n ; 
      even_natural(n) ==> even_natural(n+2);
  }
*/
