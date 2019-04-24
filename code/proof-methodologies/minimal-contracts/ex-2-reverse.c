#include <stddef.h>

void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

void reverse(int* array, size_t len){
  for(size_t i = 0 ; i < len/2 ; ++i){
    swap(array+i, array+len-i-1) ;
  }
}
