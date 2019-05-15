#include <stdbool.h>

bool cells[10];

/*@
  logic set<int> singleton(int i) = i;
*/


/*@
  axiomatic allocation{
    logic set<int> allocated{L} reads cells[0 .. 9];
    axiom definition{L}:
      \forall int i; \subset(singleton(i) , allocated) <==> cells[i] == true;
  }
*/


/*@
  lemma x:
  \forall int i; 
  0 <= i < 10 && cells[i] == false ==> ! \subset(singleton(i), allocated);
*/

/*@
  assigns cells[0 .. 9];
  ensures allocated == \empty;
*/
void init(){
  /*@
    loop invariant 0 <= i <= 10;
    loop invariant \forall integer j; 0 <= j < i ==> cells[j] == false;
    loop assigns i, cells[0 .. 9];
    loop variant 10 - i;
  */
  for(int i = 0; i < 10; ++i)
    cells[i] = false;
}


int alloc(){
  return 1;
}


int main(){
}
