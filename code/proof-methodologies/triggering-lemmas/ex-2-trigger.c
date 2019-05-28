/*@
  axiomatic Ax {
    predicate X{L1, L2}(int* p, integer l)
        reads \at(p[0 .. l-1], L1), \at(p[0 .. l-1], L2) ;
    predicate Y{L1, L2}(int* p, integer l)
        reads \at(p[0 .. l-1], L1), \at(p[0 .. l-1], L2) ;

    axiom Ax_axiom_XY {L1,L2}:
      \forall int* p, integer l, i ; 0 <= i <= l ==> X{L1, L2}(p, i) ==> Y{L1, L2}(p, l) ;
    axiom transitive{L1,L2,L3}:
      \forall int* p, integer l ; Y{L1,L2}(p, l) ==> Y{L2,L3}(p, l) ==> Y{L1,L3}(p, l);
  }
*/

/*@
  assigns p[0 .. l-1] ;
  ensures X{Pre, Post}(p, l) ;
*/
void f(int* p, unsigned l);

/*@
  ensures Y{Pre,Post}(p, l);
*/
void g(int* p, unsigned l){
  f(p, l) ;
  f(p, l) ;
}
