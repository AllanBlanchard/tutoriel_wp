Logic functions are meant to describe functions that can only be used in
specifications. It allows us, first, to factor those specifications and, second,
to define some operations on `integer` or `real` with the guarantee that they
cannot overflow since they are mathematical types.

Like predicates, they can receive different labels and values in parameter.

# Syntax

To define a logic function, the syntax is the following:

```c
/*@
  logic return_type my_function{ Label0, ..., LabelN }( type0 arg0, ..., typeN argN ) =
    formula using the arguments ;
*/
``` 

We can for example define a mathematical [linear function](https://en.wikipedia.org/wiki/Linear_function_(calculus)) using a logic function:

```c
/*@
  logic integer ax_b(integer a, integer x, integer b) =
    a * x + b;
*/
```

And it can be used to prove the source code of the following function:

```c
/*@ 
  assigns \nothing ;
  ensures \result == ax_b(3,x,4); 
*/
int function(int x){
  return 3*x + 4;
}
```

![Some overflows seem to be possible](https://zestedesavoir.com:443/media/galleries/2584/e34ccc72-b7ea-46cf-9875-16c3d57262af.png)

This code is indeed proved but some runtime-errors seems to be possible. We can
again define some mathematical logic function that will provide the bounds of
the affine function according to the machine type we use (from a logic point of
view). It allows us to then add our bounds checking in the precondition of the
function.

```c
/*@
  logic integer limit_int_min_ax_b(integer a, integer b) =
    (a == 0) ? (b > 0) ? INT_MIN : INT_MIN-b :
    (a <  0) ? (INT_MAX-b)/a :
               (INT_MIN-b)/a ;

  logic integer limit_int_max_ax_b(integer a, integer b) =
    (a == 0) ? (b > 0) ? INT_MAX-b : INT_MAX :
    (a <  0) ? (INT_MIN-b)/a :
               (INT_MAX-b)/a ;
*/

/*@
  requires limit_int_min_ax_b(3,4) < x < limit_int_max_ax_b(3,4);
  assigns \nothing ;
  ensures \result == ax_b(3,x,4);
*/
int function(int x){
  return 3*x + 4;
}
```

[[information]]
| Note that, as in specifications, computations are done using mathematical
| integers. We then do not need to care about some overflow risk with the
| computation of `INT_MIN-b` or `INT_MAX-b`.

Once this specification is provided, everything is fine. Of course, we could
manually provide these bounds every time we create a linear logic function.
But, by creating these bound computation functions, we directly get a way to
compute them automatically which is quite comfortable.

# Recursive functions and limits of logic functions

Logic functions (as well as predicates) can be recursively defined. However,
such an approach will rapidly show some limits in their use for program proof.
Indeed, when the automatic solver reasons on such logic properties, if such a
function is met, it will be necessary to evaluate it. SMT solvers are not
meant to be efficient for this task, which will generally be costly, producing
too long proof resolution and eventually timeouts.

We can have a concrete example with the factorial function, using logic and
using C language:

```c
/*@
  logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);
*/

/*@ 
  assigns \nothing ;
  ensures \result == factorial(n) ; 
*/
unsigned facto(unsigned n){
  return (n == 0) ? 1 : n * facto(n-1);
}
```

Without checking overflows, this function is easy and fast to prove. If we add
runtime error checking, RTE does not add any assertion to check the absence of
overflow on unsigned integers, since it is specified by the C standard (and is then
a defined behavior). If we want to add an assertion at this point, we can ask
WP to generate its own bound checking by right-clicking on the function and then
selecting "insert WP-safety guards". And in this case, an overflow is not proved to
be absent.

On `unsigned`, the maximum value for which we can compute factorial is 12. If
we go further, it overflows. We can then add this precondition:

```c
/*@ 
  requires n <= 12 ;
  assigns \nothing ;
  ensures \result == factorial(n) ; 
*/
unsigned facto(unsigned n){
  return (n == 0) ? 1 : n * facto(n-1);
}
```

If we ask for a proof on this input, Alt-ergo will probably fail, whereas Z3 can
compute the proof in less than a second. The reason is that in this case, the
heuristics that are used by Z3 consider that it is a good idea to spend a bit
more time on the evaluation of the function. We can for example change the
maximum value of `n` to see how the different provers behave. With an `n` fixed to
9, Alt-ergo produces a proof in less than 10 seconds, whereas with a value of 10,
even a minute is not enough.

Logic functions can then be defined recursively but without some more help, we
are rapidly limited by the fact that provers will need to perform evaluation or
to "reason" by induction, two tasks for which they are not efficient. This will
limit our possibilities for program proofs.
