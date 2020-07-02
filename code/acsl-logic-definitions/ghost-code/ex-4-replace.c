#include <stddef.h>

void replace(int *a, size_t length, int old, int new) {
  for (size_t i = 0; i < length; ++i) {
    if (a[i] == old)
      a[i] = new;
  }
}

/*@
  requires \valid(a + (0 .. length-1));
  assigns a[0 .. length-1];
  ensures \forall integer i ; 0 <= i < length ==> -100 <= a[i] <= 100 ;
*/
void initialize(int *a, size_t length);

void caller(void) {
  int a[40];

  initialize(a, 40);

  //@ ghost L: ;

  replace(a, 40, 0, 42);

  // here we want to obtain the updated locations via a ghost array
}
