/* run.config
   OPT:
*/

/*@
  predicate hide_valid(int* p) = \valid(p);

  inductive P(int*p) {
  case c:
    \forall int* p ; hide_valid(p) && p == (void*)0 ==> P(p) ;
  }
*/

int n ;

/*@
  requires P(&n) ;
  ensures  \false ;
*/
void function(int n){

}
