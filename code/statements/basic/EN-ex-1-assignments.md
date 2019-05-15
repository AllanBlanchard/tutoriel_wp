```c
/*@
  requires -10 <= x <= 0 ;
  requires 0 <= y <= 5 ;
  ensures -10 <= \result <= 10 ;
*/
int function(int x, int y){
  int res ;
  y += 10 ;
  x -= 5 ;
  res = x + y ;
  return res ;
}
```

```
wp(
  y += 10 ;
  x -= 5 ;
  res = x + y ; ,
  -10 <= res <= 10)  --> (* BY SEQUENCE *)
wp(
  y += 10,
  wp(
    x -= 5 ;
    res = x + y ; ,
    -10 <= res <= 10)) --> (* BY SEQUENCE *)
wp(
  y += 10,
  wp(
    x -= 5 ; ,
    wp(
      res = x + y ; ,
      -10 <= res <= 10))) --> (* BY ASSIGNMENT *)
wp(
  y += 10,
  wp(
    x -= 5 ; ,
    -10 <= x + y <= 10)) --> (* BY ASSIGNMENT *)
wp(
  y += 10,
 -10 <= x - 5 + y <= 10) --> (* BY ASSIGNMENT *)

-10 <= x - 5 + y + 10 <= 10 -->
-5 <= x + y <= 15
```

The actual precondition of the function is:

```
-10 <= x <= 0 ;
0 <= y <= 5 ;
```

Thus:

```
-10 <= x+y <= 5
```

And since:

```
-10 <= x+y <= 5 ==> -5 <= x + y <= 15
```

By the consequence rule the function is correct.