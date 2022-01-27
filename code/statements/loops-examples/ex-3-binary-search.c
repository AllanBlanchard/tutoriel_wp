/* run.config
   OPT:
*/

#include <stddef.h>

/*@
  requires Sorted:
    \forall integer i, j ; 0 <= i <= j < len ==> arr[i] <= arr[j] ;
*/
int bsearch(int* arr, int len, int value){
  if(len == 0) return -1 ;

  int low = 0 ;
  int up = len-1 ;

  while(low <= up){
    int mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid-1 ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return -1 ;
}
