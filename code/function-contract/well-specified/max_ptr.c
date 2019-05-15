/*@
  requires \valid_read(a) && \valid_read(b);

  assigns  \nothing;

  ensures \result == *a || \result == *b;
  ensures \result >= *a && \result >= *b;
*/
int max_ptr(int* a, int* b){
  return (*a > *b) ? *a : *b ;
}
