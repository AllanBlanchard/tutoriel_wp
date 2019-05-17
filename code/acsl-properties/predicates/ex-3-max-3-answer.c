/*@
  predicate one_of{L}(integer i, int *a, int *b, int *c) =
    \exists int* p ; p \in { a, b, c } && \at(*p, L) == i ;
*/

/*@
  requires \valid(a) && \valid(b) && \valid(c) ;
  assigns \nothing ;
  ensures one_of{Pre}(\result, a, b, c);
  ensures \result >= *a && \result >= *b && \result >= *c ;
*/
int max_of(int* a, int* b, int* c){
  if(*a >= *b && *a >= *c) return *a ;
  if(*b >= *a && *b >= *c) return *b ;
  return *c ;
}
