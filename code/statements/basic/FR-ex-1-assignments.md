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
  -10 <= res <= 10)  --> (* REGLE DE SEQUENCE *)
wp(
  y += 10,
  wp(
    x -= 5 ;
    res = x + y ; ,
    -10 <= res <= 10)) --> (* REGLE DE SEQUENCE *)
wp(
  y += 10,
  wp(
    x -= 5 ; ,
    wp(
      res = x + y ; ,
      -10 <= res <= 10))) --> (* REGLE DE L'AFFECTATION *)
wp(
  y += 10,
  wp(
    x -= 5 ; ,
    -10 <= x + y <= 10)) --> (* REGLE DE L'AFFECTATION *)
wp(
  y += 10,
 -10 <= x - 5 + y <= 10) --> (* REGLE DE L'AFFECTATION *)

-10 <= x - 5 + y + 10 <= 10 -->
-15 <= x + y <= 5
```

La précondition réelle de la fonction est ;

```
-10 <= x <= 0 ;
0 <= y <= 5 ;
```

Donc :

```
-10 <= x+y <= 5
```

Et puisque :

```
-10 <= x+y <= 5 ==> -15 <= x + y <= 5
```

Par la règle de conséquence, la fonction est correcte.
