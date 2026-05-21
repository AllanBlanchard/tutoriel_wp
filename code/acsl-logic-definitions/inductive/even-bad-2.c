/* run.config
   OPT:
*/

/*@
  inductive P(int*p) {
  case c:
    \forall int* p ; \valid(p) && p == (void*)0 ==> P(p) ;
  }
*/

int n;

/*@
  requires P(&n) ;
  ensures  \false ;
*/
void function(void){

}
