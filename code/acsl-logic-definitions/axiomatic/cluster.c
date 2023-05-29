/* run.config
   OPT:
*/

/*@ axiomatic X {
      predicate P(int* x) reads *x;
      axiom x: \forall int *x ; *x == 0 ==> P(x) ;
    }
*/

/*@ axiomatic Y {
      predicate Q(int *x) reads *x ;
      axiom y: \forall int *x ; *x == 0 ==> P(x) && Q(x) ;
    }
*/

//@ ensures P(p) ;
void function(int* p){}
