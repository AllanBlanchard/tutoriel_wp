/* run.config
   STDOPT:+"-wp-prover alt-ergo,z3"
*/

/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0);
  case even_not_nul_natural{L}:
    \forall integer n ;
      even_natural(n) ==> even_natural(n+2);
  }
*/

void foo(){
  //@ assert even_natural(4);
  //@ assert even_natural(42);
}

void bar(){
  int a = 1 ;
  //@ assert !even_natural(a);
}
