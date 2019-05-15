/*@
  predicate dec{L1, L2}(int* x) =
    \at(*x, L1) > \at(*x, L2) ;
  predicate inc{L1, L2}(int* x) =
    \at(*x, L1) < \at(*x, L2) ;
*/

/*@
  axiomatic Ax {
    predicate P(int* x) reads *x ;
    predicate Q(int* x) reads *x ;

    axiom ax_1: \forall int* x ; P(x) ==> Q(x);
    axiom ax_2{L1, L2}: 
      \forall int* x ; dec{L1, L2}(x) ==> P{L1}(x) ==> P{L2}(x);
    axiom ax_3{L1, L2}: 
      \forall int* x ; inc{L1, L2}(x) ==> P{L1}(x) ==> P{L2}(x);
  }
*/

/*@
  assigns *x ; 
  behavior b_1:
    assumes *x < 0 ;
    ensures *x >= 0 ;
  behavior b_2:
    assumes *x >= 0 ;
    ensures *x < 0 ;
  complete behaviors ;
  disjoint behaviors ;
*/
void g(int* x);

/*@
  requires P(x) ;
  ensures  Q(x) ;
*/
void example(int* x){
  g(x);
  //@ assert *x >= 0 ==> inc{Pre, Here}(x);
  //@ assert *x < 0 ==> dec{Pre, Here}(x);
}
