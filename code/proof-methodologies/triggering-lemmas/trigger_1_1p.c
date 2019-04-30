/*@
  axiomatic Ax {
    predicate P(int* x) reads *x ;
    predicate Q(int* x) reads *x ;

    axiom ax_1: \forall int* x ; P(x) ==> Q(x);
    axiom ax_2{L1, L2}: 
      \forall int* x ; \at(*x, L1) == \at(*x, L2) ==> P{L1}(x) ==> P{L2}(x);
  }
*/

/*@ assigns *x ; */
void g(int* x);

/*@
  requires \separated(x, y);
  requires P(x) ;
  ensures  Q(x) ;
*/
void example(int* x, int* y){
  g(y);
  //@ assert P(x);
}
