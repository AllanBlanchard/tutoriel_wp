/* run.config
   STDOPT:+"-wp-prover alt-ergo,z3"
*/

/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0) ;
  case even_not_nul_natural{L}:
    \forall integer n ; n > 0 ==> even_natural(n-2) ==>
      even_natural(n) ;
  }
*/

void foo(){
  int a = 42 ;
  //@ assert even_natural(a);
}


/*@
  lemma inversion{L}:
  \forall integer n ; even_natural(n) ==>
    (n > 0 && even_natural(n-2) || n == 0) ;
*/

void bar(){
  int a = 1 ;
  //@ assert !even_natural(a);
}
