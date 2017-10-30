Axioms are properties we state to be true no matter the situation. It is a good
way to state complex properties that will allow the proof process to be more
efficient by abstracting their complexity. Of course, as any property expressed
as an axiom is assumed to be true, we have to be very careful when we use them
to defined properties: if we introduce a false property in our assumptions,
"false" becomes "true" and we can then prove anything.

# Syntax

Axiomatic definitions are introduced using this syntax:
```c
/*@
  axiomatic Name_of_the_axiomatic_definition {
    // here we can define or declare functions and predicates

    axiom axiom_name { Label0, ..., LabelN }:
      // property ;

    axiom other_axiom_name { Label0, ..., LabelM }:
      // property ;

    // ... we can put as many axioms we need
  }
*/
```

For example, we can write this axiomatic block:

```c
/*@
  axiomatic lt_plus_lt{
    axiom always_true_lt_plus_lt:
      \forall integer i, j; i < j ==> i+1 < j+1 ;
  }
*/
```

And we can see that in Frama-C, this property is actually assumed to be true:


![First axiom, assumed to be true by Frama-C](/media/galleries/2584/8cd93c4d-dead-4fa9-a4ba-d9759d0e8bde.png)

[[secret]]
| Currently, our automatic solvers are not powerful enough to compute *the
| Answer to the Ultimate Question of Life, the Universe, and Everything*.
| We can help them by stating it as an axiom! Now, we just have to
| understand the question to determine in which case this result can be
| useful ...
|
| ```c
| /*@
|   axiomatic Ax_answer_to_the_ultimate_question_of_life_the_universe_and_everything {
|     logic integer the_ultimate_question_of_life_the_universe_and_everything{L} ;
| 
|     axiom answer{L}:
|       the_ultimate_question_of_life_the_universe_and_everything{L} = 42;
|   }
| */
| ```

## Link with lemmas

Lemmas and axioms allows to express the same types of properties. Namely,
properties expressed about quantified variables (and possibly global variables,
but it is quite rare since it is often difficult to find a global property about
such variables being both true and interesting). Apart this first common point,
we can also notice that when we are not considering the definition of the
lemma itself, lemmas are assumed to be true by WP exactly as axioms are.

The only difference between lemmas and axioms from a proof point of view is
that we must provide a proof that each lemma is true, whereas an axiom is
always assumed to be true.

# Recursive function or predicate definitions

Axiomatic definition of recursive functions and predicates are particularly
useful since they will prevent provers to unroll the recursion when is is
possible.

The idea is then not to define directly the function or the predicate but
to declare it and then to define axioms that will specify its behavior. If
we come back to the factorial function, we can define it axiomatically as
follows:

```c
/*@
  axiomatic Factorial{
    logic integer factorial(integer n);
    
    axiom factorial_0:
      \forall integer i; i <= 0 ==> 1 == factorial(i) ;

    axiom factorial_n:
      \forall integer i; i > 0 ==> i * factorial(i-1) == factorial(i) ;
  }
*/
```

In this axiomatic definition, our function do not have a body. Its behavior is
only defined by the axioms we have stated about it.

A small subtlety is that we must take care about the fact that if some axioms
state properties about the content of some pointed memory cells, we have to
specify considered memory blocks using the `reads` notation in the declaration.
If we omit such a specification, the predicate or function will be considered
to be stated about the received pointers and not about pointer memory blocks.
So, if the code modifies the content of an array for which we had proven that
the predicate or function give some result, this result will not be considered
to be potentially different.

If, for example, we want to define that an array only contains 0s, we have to
write it as follows:

```c
/*@
  axiomatic A_all_zeros{
    predicate zeroed{L}(int* a, integer b, integer e) reads a[b .. e-1];

    axiom zeroed_empty{L}:
      \forall int* a, integer b, e; b >= e ==> zeroed{L}(a,b,e);

    axiom zeroed_range{L}:
      \forall int* a, integer b, e; b < e ==>
        zeroed{L}(a,b,e-1) && a[e-1] == 0 <==> zeroed{L}(a,b,e);
  }
*/
```

And we can again prove that our memset to 0 is correct with this new
definition:

```c
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  zeroed(array,0,length);
*/
void memset0(int* array, size_t length){
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

Then we can add an assertion to specify what did not change between the beginning
of the loop block (pointed by the label `L` in the code) and the end (which is
`Here` since we state the property at the end):

```c
for(size_t i = 0; i < length; ++i){
  L:
  array[i] = 0;
  //@ assert same_elems{L,Here}(array,0,i);
}
```

Note that in this new version of the code, the property stated by our lemma is
not proved using automatic solver, that cannot reason by induction. If the reader
is curious, the (quite simple) Coq proof can be found there:

[[secret]]
| ```coq
| (* Generated by WP *)
| Definition P_same_elems (Mint_0 : farray addr Z) (Mint_1 : farray addr Z)
|     (a : addr) (b : Z) (e : Z) : Prop :=
|     forall (i : Z), let a_1 := (shift_sint32 a i%Z) in ((b <= i)%Z) ->
|       ((i < e)%Z) -> (((Mint_0.[ a_1 ]) = (Mint_1.[ a_1 ]))%Z).
| Goal
|   forall (i_1 i : Z), forall (t_1 t : farray addr Z), forall (a : addr),
|     ((P_zeroed t a i_1%Z i%Z)) -> ((P_same_elems t_1 t a i_1%Z i%Z)) -> ((P_zeroed t_1 a i_1%Z i%Z)).
| (* Our proof *)
| Proof.
|   intros b e.
|   (* by induction on the distance between b and e *)
|   induction e using Z_induction with (m := b) ; intros mem_l2 mem_l1 a Hz_l1 Hsame.
|   (* Base case: "empty axiom" *)
|   + apply A_A_all_zeros.Q_zeroed_empty ; assumption.
|   + replace (e + 1) with (1 + e) in * ; try omega.
|     (* we use range axiom *)
|     rewrite A_A_all_zeros.Q_zeroed_range in * ; intros Hinf.
|     apply Hz_l1 in Hinf ; clear Hz_l1 ; inversion_clear Hinf as [Hlast Hothers].
|     split.
|     (* sub range considered by Hsame *)
|     - rewrite Hsame ; try assumption ; omega.
|     (* induction hypotheses *)
|     - apply IHe with (t := mem_l1) ; try assumption.
|       * unfold P_same_elems ; intros ; apply Hsame ; omega.
| Qed.
| ```

In this case study, using an axiomatic definition is not efficient: our
property can be perfectly expressed using the basic constructs of the first
order logic as we did before. Axiomatic definitions are meant to be used to
write definitions that are not easy to express using the basic formalism
provided by ACSL. It is here used to illustrate their use with a simple
example.

# Consistency

By adding axioms to our knowledge base, we can produce more complex proofs since
some part of these proofs, expressed by axioms, do not need to be proved anymore
(they are already specified to be true) shortening the proof process. However,
using axiomatic definitions, **we must be extremely careful**. Indeed, even a
small error could introduce false in the knowledge base, making our whole
reasoning futile. Our reasoning would still be correct, but relying on false
knowledge, it would only learn incorrect things.

The simplest example is the following:

```c
/*@
  axiomatic False{
    axiom false_is_true: \false;
  }
*/

int main(){
  // Examples of proven properties

  //@ assert \false;
  //@ assert \forall integer x; x > x;
  //@ assert \forall integer x,y,z ; x == y == z == 42;
  return *(int*) 0;
}
```

And everything is proved, comprising the fact that the dereferencing of 0
is valid:

![Different false things proved to be true](https://zestedesavoir.com:443/media/galleries/2584/8bb12c3f-5da7-4f44-a889-fa5df0ab8e7a.png)

Of course, this example is extreme, we would not write such an axiom. The
problem is in fact that it is really easy to write an axiomatic definition
that is subtly false when we express more complex properties, or adding
assumptions about the global state of the system.

When we start to create axiomatic definitions, it is worth adding assertions
or postconditions requiring a proof of false that we expect to fail to ensure
that the definition is not inconsistent. However, it is often not enough! If
the subtlety that creates the inconsistency is hard enough to find, provers
could need a lot of information other than the axiomatic definition itself to
be able to find and use the inconsistency, we then need to always be careful!

More specifically, specifying the values read by a function or a predicate is
important for the consistency of an axiomatic definition. Indeed, as previously
explained, if we do not specify what is read when a pointer is received, an
update of a value inside the array do not invalidate a property known about the
content of the array. In such a case, the proof is performed but since the
axiom do not talk about the content of the array, we do not prove anything.

For example, in the function that memset an array to 0, if we modify the
axiomatic definition, removing the specification of the values that are read
by the predicate (```reads a[b .. e-1]```), the proof will still be performed,
but will not prove anything about the content of the arrays.

# Example: counting occurrences of a value

In this example, we want to prove that an algorithm actually counts the
occurrences of a value inside an array. We start by axiomatically define
what is the number of occurrences of a value inside an array:

```c
/*@
  axiomatic Occurrences_Axiomatic{
    logic integer l_occurrences_of{L}(int value, int* in, integer from, integer to)
      reads in[from .. to-1];

    axiom occurrences_empty_range{L}:
      \forall int v, int* in, integer from, to;
        from >= to ==> l_occurrences_of{L}(v, in, from, to) == 0;

    axiom occurrences_positive_range_with_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[to-1] == v) ==>
      l_occurrences_of(v,in,from,to) == 1+l_occurrences_of(v,in,from,to-1);

    axiom occurrences_positive_range_without_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[to-1] != v) ==>
      l_occurrences_of(v,in,from,to) == l_occurrences_of(v,in,from,to-1);
  }
*/
```

We have three different cases:

- the considered range of values is empty: the number of occurrences is 0,
- the considered range of values is not empty and the last element is the one we
  are searching: the number of occurrences is the number of occurrences in the
  current range without the last element, plus 1,
- the considered range of values is not empty and the last element is not the one
  we are searching: the number of occurrences is the number of occurrences in the
  current range without the last element.

Then, we can write the C function that computes the number of occurrences of a
value inside an array and prove it:

```c
/*@
  requires \valid_read(in+(0 .. length));
  assigns  \nothing;
  ensures  \result == l_occurrences_of(value, in, 0, length);
*/
size_t occurrences_of(int value, int* in, size_t length){
  size_t result = 0;
  
  /*@
    loop invariant 0 <= result <= i <= length;
    loop invariant result == l_occurrences_of(value, in, 0, i);
    loop assigns i, result;
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    result += (in[i] == value)? 1 : 0;

  return result;
}
```

An alternative way to specify, in this code, that `result` is at most `i`,
is to express a more general lemma about the number of occurrences of a
value inside an array, since we know that it is comprised between 0 and the
size of maximum considered range of values:

```c
/*@
lemma l_occurrences_of_range{L}:
  \forall int v, int* array, integer from, to:
    from <= to ==> 0 <= l_occurrences_of(v, a, from, to) <= to-from;
*/
```

An automatic solver cannot discharge this lemma. It would be necessary to prove
it interactively using Coq, for example. By expressing, generic manually proved
lemmas, we can often add useful tools to provers to manipulate more efficiently
our axiomatic definitions, without directly adding new axioms that would augment
the chances to introduce errors. Here, we still have to realize the proof of the
lemma to have a complete proof.

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
is a interesting use case for axiomatic definitions.

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

Defining the notion of permutation is easily done using an axiomatic definition.
Indeed, to determine that an array is the permutation of an other one, we can
limit us to a few cases. First, the array is a permutation of itself, then
swapping to values of the array produces a new permutation if we do not change
anything else. And finally if we create the permutation $p_2$ of $p_1$, and then
the permutation $p_3$ of $p_2$, then by transitivity $p_3$ is a permutation of
$p_1$.

The corresponding axiomatic definition is the following:

```c
/*@
  predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) && \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==> \at(a[k], L1) == \at(a[k], L2);

  axiomatic Permutation{
    predicate permutation{L1,L2}(int* a, integer b, integer e)
     reads \at(*(a+(b .. e - 1)), L1), \at(*(a+(b .. e - 1)), L2);

    axiom reflexive{L1}: 
      \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);

    axiom swap{L1,L2}:
      \forall int* a, integer b,e,i,j ;
        swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);
	
    axiom transitive{L1,L2,L3}:
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
    loop invariant \forall integer j,k; beg <= j < i ==> i <= k < end ==> a[j] <= a[k];
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
of view. This is the topic of the next section.