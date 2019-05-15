#include <limits.h>

/*@
  requires \valid(a) && \valid_read(b);
  requires \separated(a,b);
  assigns  *a;
  ensures  *a == \old(*a)+ *b;
  ensures  *b == \old(*b);
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
