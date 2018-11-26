Behind this title, that seems to be an action movie, we find in fact a way to
enrich our specification with information expressed as regular C code. Here, the
idea is to add variables and source code that will not be part of the actual
program but will model logic states that will only be visible from a proof point
of view. Using it, we can make explicit some logic properties that were
previously only known implicitly.

# Syntax

Ghost code is added using annotations that will contain C code introduced
using the `ghost` keyword:

```c
/*@
  ghost
  // C source code
*/
```

The only rules we have to respect in such a code, is that we cannot write a
memory block that is not itself defined in ghost code, and that the code must
close any block it would open. Apart of this, any computation can be inserted
provided it *only* modifies ghost variables.

Here are some examples of ghost code:

```c
//@ ghost int ghost_glob_var = 0;

void foo(int a){
  //@ ghost int ghost_loc_var = a;

  //@ ghost Ghost_label: ;
  a = 28 ;

  //@ ghost if(a < 0){ ghost_loc_var = 0; }

  //@ assert ghost_loc_var == \at(a, Ghost_label) == \at(a, Pre);
}
```

We must again be careful using ghost code. Indeed, the tool will not perform
any verification to ensure that we do not write in the memory of the program by
mistake. This problem being, in fact, an undecidable problem, this analysis would
require a proof by itself. For example, this code is allowed as input of
Frama-C even if it explicitly modifies the state of the program we want to
verify:

```c
int a;

void foo(){
  //@ ghost a = 42;
}
```

We then need to be really careful about what we are doing using ghost code (by
making it simple).

# Make a logical state explicit

The goal of ghost code is to make explicit some information that are without
them implicit. For example, in the previous section, we used it to get an
explicit logic state known at a particular point of the program.

Let us take a more complex example. Here, we want to prove that the following
function returns the value of the maximal sum of subarrays of a given array.
A subarray of an array `a` is a contiguous subset of values of `a`. For example,
for an array `{ 0 , 3 , -1 , 4 }`, some subarrays can be `{}`, `{ 0 }`,
`{ 3 , -1 }`, `{ 0 , 3 , -1 , 4 }`, ... Note that as we allow empty arrays for
subarrays, the sum is at least 0. In the previous array, the subarray with
the maximal sum is `{ 3 , -1 , 4 }`, the function would then return 6.

```c
int max_subarray(int *a, size_t len) {
  int max = 0;
  int cur = 0;
  for(size_t i = 0; i < len; i++) {
    cur += a[i];
    if (cur < 0)   cur = 0;
    if (cur > max) max = cur;
  }
  return max;
}
```

In order to specify the previous function, we will need an axiomatic definition
about sum. This is not too complex, the careful reader can express the
needed axioms as an exercise:

```c
/*@ axiomatic Sum {
  logic integer sum(int *array, integer begin, integer end) reads a[begin..(end-1)];
}*/
```

Some correct axioms are hidden there:

[[secret]]
| ```c
| /*@
|   axiomatic Sum_array{
|     logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
|    
|     axiom empty: 
|       \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
|     axiom range:
|       \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1)+a[e-1];
|   }
| */
| ```

The specification of the function is the following:

```c
/*@ 
  requires \valid(a+(0..len-1));
  assigns \nothing;
  ensures \forall integer l, h;  0 <= l <= h <= len ==> sum(a,l,h) <= \result;
  ensures \exists integer l, h;  0 <= l <= h <= len &&  sum(a,l,h) == \result;
*/
```

For any bounds, the value returned by the function must be greater or equal to
the sum of the elements between these bounds, and there must exist some bounds
such that the returned value is exactly the sum of the elements between these
bounds. About this specification, when we want to add the loop invariant, we
will realize that we miss some information. We want to express what are the
values `max` and `cur` and what are the relations between them, but we cannot
do it!

Basically, our postcondition needs to know that there exists some bounds `low`
and `high` such that the computed sum corresponds to these bounds. However, in
our code, we do not have anything that express it from a logic point of view,
and we cannot *a priori* make the link between this logical formalization. We
will then use ghost code to record these bounds and express the loop invariant.

We will first need two variables that will allow us to record the bounds of
the maximum sum range, we will call them `low` and `high`. Every time we will
find a range where the sum is greater than the current one, we will update our
ghost variables. This bounds will then corresponds to the sum currently stored
by `max`. That induces that we need other bounds: the ones that corresponds 
to the sum store by the variable `cur` from which we will build the bounds
corresponding to `max`. For these bounds, we will only add a single ghost
variable: the current low bound `cur_low`, the high bound being the variable
`i` of the loop.

```c
/*@ 
  requires \valid(a+(0..len-1));
  assigns \nothing;
  ensures \forall integer l, h;  0 <= l <= h <= len ==> sum(a,l,h) <= \result;
  ensures \exists integer l, h;  0 <= l <= h <= len &&  sum(a,l,h) == \result;
*/
int max_subarray(int *a, size_t len) {
  int max = 0;
  int cur = 0;
  //@ ghost size_t cur_low = 0; 
  //@ ghost size_t low = 0;
  //@ ghost size_t high = 0; 

  /*@ 
    loop invariant BOUNDS: low <= high <= i <= len && cur_low <= i;
    
    loop invariant REL :   cur == sum(a,cur_low,i) <= max == sum(a,low,high);
    loop invariant POST:   \forall integer l;    0 <= l <= i      ==> sum(a,l,i) <= cur;
    loop invariant POST:   \forall integer l, h; 0 <= l <= h <= i ==> sum(a,l,h) <= max;
   
    loop assigns i, cur, max, cur_low, low, high;
    loop variant len - i; 
  */
  for(size_t i = 0; i < len; i++) {
    cur += a[i];
    if (cur < 0) {
      cur = 0;
      /*@ ghost cur_low = i+1; */
    }
    if (cur > max) {
      max = cur;
      /*@ ghost low = cur_low; */
      /*@ ghost high = i+1; */
    }
  }
  return max;
}
```

The invariant `BOUNDS` expresses how the different bounds are ordered during the
computation. The invariant `REL` expresses what the variables `cur` and `max`
mean depending on the bounds. Finally, the invariant `POST` allows us to create
a link between the invariant and the postcondition of the function.

The reader can verify that this function is indeed correctly proved without RTE
verification. If we add RTE verification, the overflow on the variable `cur`,
that is the sum, seems to be possible (and it is indeed the case).

Here, we will not try to fix this because it is not the topic of this example.
The way we can prove the absence of RTE here strongly depends on the context
where we use this function. A possibility is to strongly restrict the contract,
forcing some properties about values and the size of the array. For example,
we could strongly limit the maximal size of the array and strong bounds on
each value of the different cells. An other possibility would be to add an
error value in case of overflow ($-1$ for example), and to specify that when
an overflow is produced, this value is returned.