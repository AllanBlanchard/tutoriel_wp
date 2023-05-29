/* run.config
   OPT:
*/

/*@ axiomatic X {
      predicate P(int* p) reads *p;
      axiom x: \forall int *p ; *p == 0 ==> P(p) ;
    }
*/

/*@ axiomatic Y {
      predicate Q(int *p) reads *p ;
      axiom y: \forall int *p ; *p == 0 ==> P(p) && Q(p) ;
    }
*/

//@ ensures P(p) ;
void function(int* p){}
