Sometimes, a function can have different behaviors that can be quite different
depending on the input. Typically, a function can recieve a pointer to an
optional resource: if the pointer is `NULL`, we will have a certain behavior,
which will be different of the behavior expected when the pointer is not `NULL`.

We have already seen a function that have different behaviors: the `abs`
function. We will use it again to illustrate behaviors. We have two behaviors
for the `abs` function: either the input is positive or it is negative.

Behaviors allow us to specify the different cases for postconditions.
We introduce them using the `behavior` keyword. Each behavior will have a
name, the assumptions we have for the given case introduced with the clause
`assumes` and the associated postcondition.  Finally, we can ask WP to verify
that behaviors are disjoint (to guarantee determinism) and complete.

Behaviors are disjoint if for any (valid) input of the function, it
corresponds to the assumption (`assumes`) of a single behavior. Behaviors
are complete if any (valid) input of the function corresponds to at least
one behavior.

For example, for `abs` we have :


```c
/*@
  requires val > INT_MIN;
  assigns  \nothing;

  behavior pos:
    assumes 0 <= val;
    ensures \result == val;
  
  behavior neg:
    assumes val < 0;
    ensures \result == -val;
 
  complete behaviors;
  disjoint behaviors;
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

It can be useful to experiment two possibilities to understand the exact
meaning of `complete` and `disjoint`:

- replace the assumption of `pos` with `val > 0`, in this case, behaviors
  will be disjoint but incomplete (we will miss `val == 0`),
- replace the assumption of `neg` with `val <= 0`, in this case, behaviors
  will be complete but not disjoint (we will have two assumption corresponding
  to `val == 0`.

[[attention]]
| Even if `assigns` is a postcondition, it is to our knowledge not possible to
| indicate different `assigns` to each behaviors. If we need to specify this,
| we will:
|
| - put our `assigns` before the behaviors (as we have done in our example)
|   with all potentially modified non-local element,
| - add in post-condition of each behaviors the elements that are in fact
|   not modified by indicating there new value to be equal to the `\old` one.

Behaviors are useful to simplify the writing of specifications when functions
can jave very different behaviors depending on their input. Without them,
specification would be defined using implications expressing the same idea
but harder to write and read (which would be error-prone).

On the other hand, the translation of completness and disjointness would be
necessarily written by hand which would be tedious and again error-prone.