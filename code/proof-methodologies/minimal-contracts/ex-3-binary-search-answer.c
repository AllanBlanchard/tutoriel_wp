#include <stddef.h>

/*@
  requires \valid_read(arr + (0 .. len-1));
  assigns \nothing ;
*/
size_t bsearch(int* arr, size_t len, int value){
  if(len == 0) return -1 ;
  
  size_t low = 0 ;
  size_t up = len ;

  /*@
    loop invariant 0 <= low && up <= len ;
    loop assigns low, up ;
    loop variant up - low ;
  */
  while(low < up){
    size_t mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return -1 ;
}
