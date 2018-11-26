# Examples with read-only arrays

The Array is the most common data structure when we are working with loops. It is
then a good example base to exercise with loops, and these examples allow to
rapidly show interesting invariants and will allow us to introduce some
important ACSL constructs.

We can for example use the search function that allows to find a value inside
an array:

```c
#include <stddef.h>

/*@
  requires 0 < length;
  requires \valid_read(array + (0 .. length-1));
  
  assigns  \nothing;

  behavior in:
    assumes \exists size_t off ; 0 <= off < length && array[off] == element;
    ensures array <= \result < array+length && *\result == element;

  behavior notin:
    assumes \forall size_t off ; 0 <= off < length ==> array[off] != element;
    ensures \result == NULL;

  disjoint behaviors;
  complete behaviors;
*/
int* search(int* array, size_t length, int element){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i ==> array[j] != element;
    loop assigns i;
    loop variant length-i;
  */ 
  for(size_t i = 0; i < length; i++)
    if(array[i] == element) return &array[i];
  return NULL;
}
```

There are enough ideas inside this example to introduce some important syntax.

First, as we previously presented, the `\valid_read` predicate (as well as
`\valid`) allows us to specify not only the validity of read-only address but
also to state that a range of contiguous addresses is valid. It is expressed
using this expression:

```c
//@ requires \valid_read(a + (0 .. length-1));
```

This precondition states that all addresses a+0, a+1, ..., a+length-1 are
valid read-only locations.

We also introduced two notations that are used almost all the time in ACSL,
the keywords `\forall` ($\forall$) and `\exists` ($\exists$), the universal
logic quantifiers. The first allows to state that for any element, some
property is true, the second allows to say that there exists some element such
that the property is true. If we comment a little bit the corresponding lines
in our specification, we can read them this way:

```c
/*@
// for all "off" of type "size_t", such that IF "off" is comprised between 0 and "length"
//                                 THEN the cell "off" in "a" is different from "element"
\forall size_t off ; 0 <= off < length ==> a[off] != element;

// there exists "off" of type "size_t", such that "off" is comprised between 0 and "length"
//                                      AND the cell "off" in "a" equals to "element"
\exists size_t off ; 0 <= off < length && a[off] == element;
*/
```

If we want to summarize the use of these keywords, we would say that on a range of
values, a property is true, either about at least one of them or about all of
them. A common scheme is to constrain this set using another property
(here: `0 <= off < length`) and to prove the actual interesting property on this
smaller set. **But using `exists` and `forall` is fundamentally different**.

With `\forall type a ; p(a) ==> q(a)`, the constraint `p` is followed by an
implication. For any element where a first property `p` is verified, we have
to also verify the second property `q`. If we use a conjunction, as we do for
"exists" (which we will later explain), that would mean that all elements verify
both `p` and `q`. Sometimes, it could be what we want to express, but it would
then not correspond anymore to the idea of constraining a set for which we want
to verify some other property.

With `\exists type a ; p(a) && q(a)`, the constraint `p` is followed by a
conjunction. We say there exists an element such that it satisfies the property
`p` at the same time it also satisfies `q`. If we use an implication, as we do
for "forall", such an expression will always be true if `p` is not a tautology!
Why? Is there an "a" such that p(a) implies q(a)? Let us take an "a" such that
p(a) is false, then the implication is true.

This part of the invariant deserves a particular attention:

```c
//@ loop invariant \forall size_t j; 0 <= j < i ==> array[j] != element;
```

Indeed, it defines the treatment performed by our loop, it indicates to WP what
happens inside the loop (or more precisely: what we learn) along the execution.
Here, this formula indicates that at each iteration of the loop, we know that
for each memory location between 0 and the next location to visit
(`i` excluded), the memory location contains a value different from the element we
are looking for.

The proof obligation associated to the preservation of this invariant is a bit
complex and it is not really interesting to precisely look at it, on the
contrary, the proof that the invariant is established before executing the loop
is interesting:

![Trivial goal](https://zestedesavoir.com:443/media/galleries/2584/eda30413-2d95-4d0a-ab5c-f36a356ad516.png)

We note that this property, while quite complex, is proved easily by
Qed. If we look at the parts of the programs on which the proof relies, we can
see that the instruction `i = 0` is highlighted and this is, indeed, the last
instruction executed on `i` before we start the loop. And consequently, if we
replace the value of `i` by 0 inside the formula of the invariant, we get:

" For all j, greater or equal to 0 and strictly lower than 0 ", this part of the
formula is necessarily false, our implication is then necessarily true.

# Examples with mutable arrays

Let us present two examples with mutation of arrays. One with a mutation of all
memory locations, the other with selective modifications.

## Reset

Let us have a look at the function that resets an array of integer to 0.

```c
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  \forall size_t i; 0 <= i < length ==> array[i] == 0;
*/
void reset(int* array, size_t length){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i ==> array[j] == 0;
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    array[i] = 0;
}
```

Let us just highlight the function and loop assign clauses. Again, we can
use the notation `n .. m` to indicate which parts of the array are modified.

## Search and replace

The last example we will detail to illustrate the proof of functions with
loops is the algorithm "search and replace". This algorithm will selectively
modify values in a range of memory locations. It is generally harder to guide
the tool in such a case, because on one hand we must keep track of what is
modified and what is not, and on the other hand, the induction relies on this
fact.

As an example, the first specification we can write for this function would
look like this:

```c
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns array[0 .. length-1];

  ensures \forall size_t i; 0 <= i < length && \old(array[i]) == old
             ==> array[i] == new;
  ensures \forall size_t i; 0 <= i < length && \old(array[i]) != old 
             ==> array[i] == \old(array[i]);
*/
void search_and_replace(int* array, size_t length, int old, int new){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) == old 
                     ==> array[j] == new;
    loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) != old 
                     ==> array[j] == \at(array[j], Pre);
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i){
    if(array[i] == old) array[i] = new;
  }
}
```

We use the logic function '\at(v, Label)` that gives us the value of the
variable `v` at the program point `Label`.  If we look at the usage of this
function here, we see that in the invariant we try to establish a relation
between the old values of the array and the potentially new values:

```c
/*@
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) == old 
                   ==> array[j] == new;
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) != old 
                   ==> array[j] == \at(array[j], Pre);
*/
```

For every memory location that contained the value to be replaced, it now must
contain the new value. All other values must remain unchanged. In fact, if we
try to prove this invariant with WP, it fails. In such a case, the simpler
method is to add different assertions that will express the different
intermediate properties using assertions which we expect to be easily proved
and which imply the invariant. Here, we can easily notice that WP does not
succeed in maintaining the knowledge that we have not modified the remaining
part of the array yet:

```c
for(size_t i = 0; i < length; ++i){
    //@assert array[i] == \at(array[i], Pre); // proof failure
    if(array[i] == old) array[i] = new;
}
```

We can add this information as an invariant:

```c
/*@
  loop invariant 0 <= i <= length;
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) == old 
                   ==> array[j] == new;
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) != old 
                   ==> array[j] == \at(array[j], Pre);

  // The end of the array remains the same:
  loop invariant \forall size_t j; i <= j < length
                     ==> array[j] == \at(array[j], Pre);
  loop assigns i, array[0 .. length-1];
  loop variant length-i;
*/
for(size_t i = 0; i < length; ++i){
  if(array[i] == old) array[i] = new;
}
```

And this time the proof will succeed. Note that if we try to prove this
invariant directly with the verification of the absence of RTE, Alt-Ergo
may not succeed (CVC4 succeeds without problem). In this case, we can launch
these proofs separately (first without, and then with the absence of RTE
checking) or else add assertions that allows to guide the proof inside the
loop:

```c
for(size_t i = 0; i < length; ++i){
  if(array[i] == old) array[i] = new;

  /*@ assert \forall size_t j; i < j < length 
               ==> array[j] == \at(array[j], Pre);                      */
  /*@ assert \forall size_t j; 0 <= j <= i && \at(array[j], Pre) == old 
               ==> array[j] == new;                                     */
  /*@ assert \forall size_t j; 0 <= j <= i && \at(array[j], Pre) != old 
               ==> array[j] == \at(array[j], Pre);                      */    
}
```

As we will try to prove more complex properties, particularly when programs
involve loops, there will be a part of "trial and error" in order to
understand what the provers miss to establish the proof.

It can miss hypotheses. In this case, we can try to add assertions to guide the
prover. With some experience, we can read the content of the proof obligations
or try to perform the proof with the Coq interactive prover to see whether the
proof seems to be possible. Sometimes, the prover just needs more time. In such a
case, we can (sometimes a lot) augment the timeout value. Of course, the
property can be too hard for the prover, and in this case, we will have to write
the proof ourselves with an interactive prover.

Finally, the implementation can be indeed incorrect, and in this case we have to
fix it. Here, we will use test and not proof, because a test allows us to prove
the presence of a bug and to analyze this bug.
