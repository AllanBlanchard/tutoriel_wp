#include <stddef.h>

/*@ inductive permutation{L1, L2}(int *a, integer b, integer e){
  @ case nil{L1, L2}: 
  @   \forall int *a, integer b, e ; 
  @     b >= e ==> permutation{L1, L2}(a, b, e);
  @     
  @ case skip_end{L1, L2}:
  @   \forall int *a, integer b, e ;
  @     b < e ==>
  @     permutation{L1,L2}(a, b, e-1) ==>
  @     \at(a[e-1], L1) == \at(a[e-1], L2) ==>
  @       permutation{L1, L2}(a, b, e);
  @       
  @ case skip_begin{L1, L2}:
  @   \forall int *a, integer b, e ;
  @     b < e ==>
  @     permutation{L1,L2}(a, b+1, e) ==>
  @     \at(a[b], L1) == \at(a[b], L2) ==>
  @       permutation{L1, L2}(a, b, e);
  @       
  @ case rotate_right{L1, L2}:
  @   \forall int *a, integer b, e ;
  @     b < e ==>
  @     (\forall integer x ; b < x < e ==> \at(a[x], L2) == \at(a[x-1], L1)) ==>
  @     \at(a[b], L2) == \at(a[e-1], L1) ==>
  @       permutation{L1, L2}(a, b, e);
  @       
  @ case reflexive{L}:
  @   \forall int* a, integer b, e ; permutation{L, L}(a, b, e);
  @ 
  @ case transitive{L1, L2, L3}:
  @   \forall int* a, integer b, e ;
  @     permutation{L1, L2}(a, b, e) ==> permutation{L2, L3}(a, b, e) ==>
  @       permutation{L1, L3}(a, b, e);
  @ }
  @*/

/*@ predicate same_array{L1, L2}(int *a, integer b, integer e) =
  @   \forall integer i ; b <= i < e ==> \at(a[i], L1) == \at(a[i], L2);
  @*/
/*@ predicate sorted(int *a, integer b, integer e) =
  @   \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
  @*/


/*@ requires \valid(a + (beg .. end));
  @ requires 0 <= beg < end;
  @ requires sorted(a, beg, end) ;
  @ 
  @ assigns a[ beg .. end ] ;
  @ 
  @ ensures sorted(a, beg, end + 1);
  @ ensures permutation{Pre, Post}(a, beg, end + 1);
  @*/
void insert(int* a, size_t beg, size_t end){
  size_t i = end ;
  int value = a[i] ;
    
  /*@ loop invariant beg <= i <= end ;
    @ loop invariant i == end ==> sorted(a, beg, end) ;
    @ loop invariant i <  end ==> sorted(a, beg, end + 1) ;
    @ loop invariant \forall integer k ; i <= k < end ==> a[k] > value ;
    @ loop invariant \forall integer k ; beg <= k < i ==> a[k] == \at(a[k], Pre);
    @ loop invariant \forall integer k ; i < k <= end ==> a[k] == \at(a[k-1], Pre);
    @ loop assigns i, a[ beg .. end ] ;
    @ loop variant i ;
    @*/
  while(i > beg && a[i - 1] > value){
    a[i] = a[i - 1] ;
    i -- ;
  }
  a[i] = value ;

  // GHOST SPEC available soon
  size_t r = i ;
  /*@ loop invariant beg <= r <= i ;
    @ loop invariant permutation{Pre, Here}(a, r, end+1) ;
    @ loop invariant same_array{Pre, Here}(a, beg, r) ;
    @ loop assigns r;
    @ loop variant r;
    @*/
  while(r > beg){
    --r;
  }
}


/*@ requires \valid(a + (beg .. end-1));
  @ requires 0 <= beg < end;
  @ 
  @ assigns  a[beg .. end-1];
  @ 
  @ ensures sorted(a, beg, end);
  @ ensures permutation{Pre, Post}(a,beg,end);
  @*/
void insert_sort(int* a, size_t beg, size_t end){
  /*@ loop invariant sorted(a, beg, i) ; 
    @ loop invariant permutation{Pre, Here}(a, beg, end);
    @ loop invariant beg < i <= end ;
    @ loop assigns i, a[ beg .. end-1 ] ;
    @ loop variant end - i ;
    @*/
  for(size_t i = beg + 1 ; i < end ; ++i){
    //@ ghost P: ;
    insert(a, beg, i);

    // GHOST SPEC available soon
    /*@ loop invariant i+1 <= j <= end ;
      @ loop invariant permutation{P, Here}(a, beg, j);
      @ loop assigns j ;
      @ loop variant end - j;
      @*/
    for(size_t j = i+1 ; j < end ; j++);
  }
}
