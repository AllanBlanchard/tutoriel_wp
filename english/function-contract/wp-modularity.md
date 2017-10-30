The end of this part will be dedicated to function call composition, where we
will start to have a closer look to WP. We will also have a look to the way
we can split our programs in different files when we want to prove them using
WP.

Our goal will be to prove the `max_abs` function, that return the maximum
absolute value of two values:

```c
int max_abs(int a, int b){
  int abs_a = abs(a);
  int abs_b = abs(b);

  return max(abs_a, abs_b);
}
```

Let us start by (over-)splitting the function we already proved in pairs
header/source for `abs` and `max`. For `abs`, we have:

File: abs.h

```c
#ifndef _ABS
#define _ABS

#include <limits.h>

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
int abs(int val);

#endif
```

File: abs.c

```c
#include "abs.h"

int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

We can notice that we put our function contract inside the header file. The
goal is to be able to import the specification at the same time than the
declaration when we need it in another file. Indeed, WP will need it to be
able to prove that the precondition of the function is verified when we call
it.

We can create a file using the same format for the `max` function. In both
cases, we can open the source file (we do not need to specify header files
in the command line) with Frama-C and notice that the specification is indeed
associated to the function and that we prove it.

Now, we can prepare our header file for the `max_abs` function:

```c
#ifndef _MAX_ABS
#define _MAX_ABS

int max_abs(int a, int b);

#endif
```

And in the source file:

```c
#include "max_abs.h"
#include "max.h"
#include "abs.h"

int max_abs(int a, int b){
  int abs_a = abs(a);
  int abs_b = abs(b);

  return max(abs_a, abs_b);
}
```

We can open the source file in Frama-C. If we look at the side panel, we can
see that the header files we have included in `abs_max` correctly appear and
if we look at the function contracts for them, we can see some blue and green
bullets:

![The contract of `max` is assumed to be valid](https://zestedesavoir.com:443/media/galleries/2584/792fb2f6-435f-43ff-adc7-a981ae56f44a.png)

These bullets indicate that, since we do not have the implementation, they are
assumed to be true. It is an important strength of the deductive proof of
programs compared to some other formal methods: function are verified isolated
from each other.

When we are not currently performing the proof of a function, its specification
is considered to be correct: we do not try to prove it when we are proving another
function, we will only verify that the precondition is correctly established when
we call it. It provides very modular proofs and specifications that are therefore
more reusable. Of course, if our proof rely on the specification of another
function, it must be provable to ensure that the proof of the program is complete.
But, we can also consider that we trust a function that comes from an external
library that we do not want to prove (or for which we do not even have the source
code).

The careful reader could specify and prove the `max_abs` function.

A solution is provided there (we also add the implementation as a reminder):

```c
/*@
  requires a > INT_MIN;
  requires b > INT_MIN;

  assigns \nothing;

  ensures \result >= 0;
  ensures \result >= a && \result >= -a && \result >= b && \result >= -b;
  ensures \result == a || \result == -a || \result == b || \result == -b;
*/
int abs_max(int a, int b){
  int abs_a = abs(a);
  int abs_b = abs(b);

  return max(abs_a, abs_b);
}
```
