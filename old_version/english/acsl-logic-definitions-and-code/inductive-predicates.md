Inductive predicates gives a way to state properties whose verification requires
to reason by induction, that is to say: for a property $p(input)$, it is true
for some base cases (for example, $0$ is an even natural number), and knowing
that $p(input)$ is true, it also true for a $bigger input$, provided some
conditions relating $input$ and $bigger input$ (for example, knowing that $n$ is
even, we define that $n+2$ is also even). Thus, inductive predicates are
generally useful to define properties recursively.

# Syntax

For now, let us define the syntax of inductive predicates:

```c
/*@
  inductive property{ Label0, ..., LabelN }(type0 a0, ..., typeN aN) {
  case c_1{L0, ..., Lq}: p_1 ;
  ...
  case c_m{L0, ..., Lr}: p_km ;
  }
*/
```

Where all `c_i` are names and all `p_i` are logic formulas where
`property` appears has a conclusion. Basically, `property` is true for
some parameters and some labels, if it corresponds to one of the cases
of the inductive definition.

We can have a look to the simple property we just talked about: how to define
that a natural number is even using induction. We can translate the sentence:
"0 is a natural number, and if $n$ is a natural number, $n+2$ is a natural
number":

```c
/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0);
  case even_not_nul_natural{L}:
    \forall integer n ; 
      even_natural(n) ==> even_natural(n+2);
  }
*/
```

Which perfectly describes the two cases:

- $0$ is even (base case),
- if a natural $n$ is even, $n+2$ is also even.

However, this definition is not completely satisfaying. For example, we cannot
deduce that an odd number is not even. If we try to prove that 1 is even, we
will have to check if -1 is even, and then -3, -5, etc, infinitely. Moreover,
we generally prefer to define the induction cases the opposite way: defining
the condition under which the wanted conclusion is true. For example, here,
how can we verify that some $n$ is natural and even? We first have to check that
$n$ is greater than $0$ and then to verify that $n-2$ is even:

```c
/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0) ;
  case even_not_nul_natural{L}:
    \forall integer n ; n > 0 ==> even_natural(n-2) ==>
      even_natural(n) ;
  }
*/
```

Here, we distinguish two cases:

- 0 is even,
- a natural $n$ is even if $n-2$ is an even natural.

Taking the second case, we recursively decrease the number until we reach
0 - and then the number is even, since 0 is even - or -1, and then there
is no case in the inductive that corresponds to this value, so we could
deduce that the property is false (however, SMT solvers are generally not
good at reasoning by induction, but we will see how to ease this later).

[INSERT EXAMPLE OF PROOF]

Of course, defining that some natural number is even inductively is not a
good idea, since we can simply define it using modulo. We generally use them
to define complex recursive properties.

## Well-founded induction

Frédéric ! Help me !

# Recursive predicate definitions

Inductive predicates are often useful to express recursive properties since it
prevents the provers to unroll the recursion when it is possible.

If, for example, we want to define that an array only contains 0s, we have to
write it as follows:

```c
/*@
  inductive zeroed{L}(int* a, integer b, integer e){
  case zeroed_empty{L}:
    \forall int* a, integer b, e; b >= e ==> zeroed{L}(a,b,e);
  case zeroed_range{L}:
    \forall int* a, integer b, e; b < e ==>
      zeroed{L}(a,b,e-1) && a[e-1] == 0 ==> zeroed{L}(a,b,e);
  }
*/
```

And we can again prove that our reset to 0 is correct with this new
definition:

```c
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  zeroed(array,0,length);
*/
void reset(int* array, size_t length){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant zeroed(array,0,i);
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    array[i] = 0;
}
```

Depending on the Frama-C or automatic solvers versions, the proof of the
preservation of the invariant could fail. A reason to this fail is the fact that
the prover forget that cells preceding the one we are currently processing
are actually still set to 0. We can add a lemma in our knowledge base, stating
that if a set of values of an array did not change between two program points,
the first one being a point where the property "zeroed" is verified, then the
property is still verified at the second program point.

```c
/*@
  predicate same_elems{L1,L2}(int* a, integer b, integer e) =
    \forall integer i; b <= i < e ==> \at(a[i],L1) == \at(a[i],L2);

  lemma no_changes{L1,L2}:
    \forall int* a, integer b, e;
      same_elems{L1,L2}(a,b,e) ==> zeroed{L1}(a,b,e) ==> zeroed{L2}(a,b,e);
*/
```

Then we can add an assertion to specify what did not change between the
beginning of the loop block (pointed by the label `L` in the code) and the end
(which is `Here` since we state the property at the end):

```c
for(size_t i = 0; i < length; ++i){
  L:
  array[i] = 0;
  //@ assert same_elems{L,Here}(array,0,i);
}
```

Note that in this new version of the code, the property stated by our lemma is
not proved using automatic solver, that cannot reason by induction. If the
reader is curious, the (quite simple) Coq proof can be found there:

[[secret]]
| ```coq
| Goal
|   forall (i_1 i : Z),
|   forall (t_1 t : farray addr Z),
|   forall (a : addr),
|   ((P_zeroed t a i_1%Z i%Z)) ->
|   ((P_same_elems t_1 t a i_1%Z i%Z)) ->
|   ((P_zeroed t_1 a i_1%Z i%Z)).
| 
| Proof.
|   (* introduce the variables *)
|   intros first last Memory_after Memory_before array Zeroed_before Same.
|   (* by induction on our inductive property *)
|   induction Zeroed_before as 
|     (* rename the variables for the first case: empty range *)
|     [ first last array 
|     (* rename the variables for the second case: non empty range *)
|     | first last Memory_before array last_index last_value
|       bound SubZeroed_before].
|   + (* First case : *)
|     constructor 1. (* just remark that in conclusion we also have empty
|                       range *)
|     assumption.    (* and just prove that the range is empty which is an
|                       assumption *)
|   + (* Second case : *)
|     (* We do not need a separate variable *)
|     unfold last_index in * ; clear last_index.
|     constructor 2. (* we also have a non empty range in conclusion *)
|     - (* First, show that the value in the last element did not change *)
|       rewrite <- last_value. (* by replace 0 with the old memory access *)
|       symmetry ; apply Same. (* and we can apply our assumption "elements 
|                                 are the same" *)
|       * omega. (* the lower bound is a simple mathematic property *)
|       * omega. (* same for the upper bound *)
|     - omega. (* again a lower bound to prove *)
|     - (* By induction we know that in the first part of the array *)
|       (* all values are zeroes :*)
|       apply IHSubZeroed_before.
|       intros i ; intros.
|       apply Same.
|       * omega.
|       * omega.
| Qed.
| ```

In this case study, using an inductive definition is not efficient: our
property can be perfectly expressed using the basic constructs of the first
order logic as we did before. Inductive definitions are meant to be used to
write definitions that are not easy to express using the basic formalism
provided by ACSL. It is here used to illustrate their use with a simple
example.

# Example: sort

We will prove a simple selection sort:

```c
size_t min_idx_in(int* a, size_t beg, size_t end){
  size_t min_i = beg;
  for(size_t i = beg+1; i < end; ++i)
    if(a[i] < a[min_i]) min_i = i;
  return min_i;
}

void swap(int* p, int* q){
  int tmp = *p; *p = *q; *q = tmp;
}

void sort(int* a, size_t beg, size_t end){
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}
```

The reader can exercise by specifying and proving the search of the minimum and
the swap function. We hide there a correct version of these specification and
code, we will focus on the specification and the proof of the sort function that
is a interesting use case for inductive definitions.

[[secret]]
| ```c
| /*@
|   requires \valid_read(a + (beg .. end-1));
|   requires beg < end;
| 
|   assigns  \nothing;
| 
|   ensures  \forall integer i; beg <= i < end ==> a[\result] <= a[i];
|   ensures  beg <= \result < end;
| */
| size_t min_idx_in(int* a, size_t beg, size_t end){
|   size_t min_i = beg;
| 
|   /*@
|     loop invariant beg <= min_i < i <= end;
|     loop invariant \forall integer j; beg <= j < i ==> a[min_i] <= a[j];
|     loop assigns min_i, i;
|     loop variant end-i;
|   */
|   for(size_t i = beg+1; i < end; ++i){
|     if(a[i] < a[min_i]) min_i = i;
|   }
|   return min_i;
| }
| 
| /*@
|   requires \valid(p) && \valid(q);
|   assigns  *p, *q;
|   ensures  *p == \old(*q) && *q == \old(*p);
| */
| void swap(int* p, int* q){
|   int tmp = *p; *p = *q; *q = tmp;
| }
| ```

Indeed, a common error we could do, trying to prove a sort function, would
be to write this specification (which is true !):

```c
/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

/*@
  requires \valid(a + (beg .. end-1));
  requires beg < end;
  assigns  a[beg .. end-1];
  ensures sorted(a, beg, end);
*/
void sort(int* a, size_t beg, size_t end){
  /*@ //invariant */
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}
```

**This specification is true**. But if we recall correctly the part of the
tutorial about specifications, we have to *precisely* express what we expect of
the program. With this specification, we do not prove all required properties
expected for a sort function. For example, this function correctly answers to
the specification:

```c
/*@
  requires \valid(a + (beg .. end-1));
  requires beg < end;

  assigns  a[beg .. end-1];
  
  ensures sorted(a, beg, end);
*/
void fail_sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant \forall integer j; beg <= j < i ==> a[j] == 0;
    loop assigns i, a[beg .. end-1];
    loop variant end-i;
  */
  for(size_t i = beg ; i < end ; ++i)
    a[i] = 0;
}
```

Our specification does not express the fact that all elements initially found
inside the array must still be found inside the array after executing the
sort function. That is to say: the sort function produces a sorted permutation
of the original array.

Defining the notion of permutation is easily done using an inductive definition.
Indeed, to determine that an array is the permutation of an other one, we can
limit us to a few cases. First, the array is a permutation of itself, then
swapping to values of the array produces a new permutation if we do not change
anything else. And finally if we create the permutation $p_2$ of $p_1$, and then
the permutation $p_3$ of $p_2$, then by transitivity $p_3$ is a permutation of
$p_1$.

The corresponding inductive definition is the following:

```c
/*@
  predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) &&
    \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==>
      \at(a[k], L1) == \at(a[k], L2);

  inductive permutation{L1,L2}(int* a, integer b, integer e){
  case reflexive{L1}: 
    \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);
  case swap{L1,L2}:
    \forall int* a, integer b,e,i,j ;
      swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);
  case transitive{L1,L2,L3}:
    \forall int* a, integer b,e ; 
      permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==> permutation{L1,L3}(a, b, e);
  }
*/
```

We can then specify that our sort function produces the sorted permutation of
the original array and we can then prove it by providing the invariant of the
function:

```c
/*@
  requires beg < end && \valid(a + (beg .. end-1));
  assigns  a[beg .. end-1];  
  ensures sorted(a, beg, end);
  ensures permutation{Pre, Post}(a,beg,end);
*/
void sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant sorted(a, beg, i) && permutation{Begin, Here}(a, beg, end);
    loop invariant
      \forall integer j, k; beg <= j < i ==> i <= k < end ==> a[j] <= a[k];
    loop assigns i, a[beg .. end-1];
    loop variant end-i;
  */
  for(size_t i = beg ; i < end ; ++i){
    //@ ghost begin: ;
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
    //@ assert swap_in_array{begin,Here}(a,beg,end,i,imin);
  }
}
```

This time, our property is precisely defined, the proof is relatively easy to
produce, only requiring to add an assertion in the block of the loop to state
that it only performs a swap of values inside the array (and then giving
the transition to the next permutation). To define this swap notion, we use
a particular annotation (at line 16), introduced using the keyword `ghost`.
Here, the goal is to introduce a label in the code that in fact does not exists
from the program point of view, and is only visible from a specification point
of view. This is the final section of this chapter, for now let us focus on
axiomatic definitions.