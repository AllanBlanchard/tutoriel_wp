#include <stddef.h>


size_t bsearch(int* arr, size_t len, int value){
  if(len == 0) return len ;
  
  size_t low = 0 ;
  size_t up = len ;

  while(low < up){
    size_t mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return len ;
}
