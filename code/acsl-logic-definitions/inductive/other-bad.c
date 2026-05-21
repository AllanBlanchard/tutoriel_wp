/*@ inductive P(int* p){
      case c: \forall int* p ; \valid(p) && p == (void*)0 ==> P(p);
    }
*/

/*@ requires P(p);
    ensures \false ; */
void foo(int *p){}
