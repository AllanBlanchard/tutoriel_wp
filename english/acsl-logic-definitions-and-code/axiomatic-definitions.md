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

Lemmas and axioms allows to express the same kinds of properties. Namely,
properties expressed about quantified variables (and possibly global variables,
but it is quite rare since it is often difficult to find a global property about
such variables being both true and interesting). Apart this first common point,
we can also notice that when we are not considering the definition of the
lemma itself, lemmas are assumed to be true by WP exactly as axioms are.

The only difference between lemmas and axioms from a proof point of view is
that we must provide a proof that each lemma is true, whereas an axiom is
always assumed to be true.

# Recursive function or predicate definitions

Just as inductive predicates do, axiomatic recursive definitions prevent solvers
to unroll recursion during reasoning.

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

For example, if we take the inductive property we stated for "zeroed" in the
previous chapter, we can write it using an axiomatic definition, and it will be
written like this:

```c
/*@
  axiomatic A_all_zeros{
    predicate zeroed{L}(int* a, integer b, integer e) reads a[b .. e-1];

    axiom zeroed_empty{L}:
      \forall int* a, integer b, e; b >= e ==> zeroed{L}(a,b,e);

    axiom zeroed_range{L}:
      \forall int* a, integer b, e; b < e ==>
        zeroed{L}(a,b,e-1) && a[e-1] == 0 ==> zeroed{L}(a,b,e);
  }
*/
```

While it is not necessary to specify are the memory location read in an
inductive definition, we have to specify such an information for axiomatically
defined properties.

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

For example, in the function that resets an array to 0, if we modify the
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

# Example: sort, again

