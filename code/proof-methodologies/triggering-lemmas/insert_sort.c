#include <stddef.h>
#include <limits.h>

void insert(int* a, size_t beg, size_t last){
  size_t i = last ;
  int value = a[i] ;

  while(i > beg && a[i - 1] > value){
    a[i] = a[i - 1] ;
    --i ;
  }
  a[i] = value ;
}

void insertion_sort(int* a, size_t beg, size_t end){
  for(size_t i = beg+1; i < end; ++i)
    insert(a, beg, i);
}
