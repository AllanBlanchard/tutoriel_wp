```c
/*@ 
  requires -5 <= y <= 5 ; 
  requires -5 <= x <= 5 ; 
  ensures  -15 <= \result <= 25 ;
*/
int function(int x, int y){
  int res ;

  if(x < 0){
    x = 0 ;
  }
  
  if(y < 0){
    x += 5 ;
  } else {
    x -= 5 ;
  }
  
  res = x - y ;

  return res ;
}
```


```
wp(if x < 0 then x = 0 else skip ;
   if y < 0 then x += 5 else x -= 5 ;
   res = x - y ; ,
   -15 <= res <= 25) --> (* sequence *)
   
wp(if x < 0 then x = 0 else skip ; ,
   wp(if y < 0 then x += 5 else x -= 5 ;
      res = x - y ; ,
      -15 <= res <= 25)) --> (* sequence *)

wp(if x < 0 then x = 0 else skip ; ,
   wp(if y < 0 then x += 5 else x -= 5 ; ,
      wp(res = x - y ; ,
         -15 <= res <= 25))) --> (* assignment *)

wp(if x < 0 then x = 0 else skip ; ,
   wp(if y < 0 then x += 5 else x -= 5 ; ,
      -15 <= x - y <= 25)) --> (* conditional *)

wp(if x < 0 then x = 0 else skip ; ,
  (y <  0 ==> wp(x += 5, -15 <= x - y <= 25)) &&
  (y >= 0 ==> wp(x -= 5, -15 <= x - y <= 25))) --> (* Assignment (x2) *)

wp(if x < 0 then x = 0 else skip ; ,
  (y <  0 ==> -15 <= x + 5 - y <= 25) &&
  (y >= 0 ==> -15 <= x - 5 - y <= 25)) --> (* conditional *)

(x < 0 ==>
   wp(x = 0,
     (y <  0 ==> -15 <= x + 5 - y <= 25) &&
     (y >= 0 ==> -15 <= x - 5 - y <= 25))) &&
(x >= 0 ==>
   wp(skip,
     (y <  0 ==> -15 <= x + 5 - y <= 25) &&
     (y >= 0 ==> -15 <= x - 5 - y <= 25)))) --> (* Assignment *)

(x < 0 ==>
     (y <  0 ==> -15 <= 0 + 5 - y <= 25) &&
     (y >= 0 ==> -15 <= 0 - 5 - y <= 25)) &&
(x >= 0 ==>
   wp(skip,
     (y <  0 ==> -15 <= x + 5 - y <= 25) &&
     (y >= 0 ==> -15 <= x - 5 - y <= 25)))) --> (* Skip *)

(x < 0 ==>
     (y <  0 ==> -15 <= 0 + 5 - y <= 25) &&
     (y >= 0 ==> -15 <= 0 - 5 - y <= 25)) &&
(x >= 0 ==>
     (y <  0 ==> -15 <= x + 5 - y <= 25) &&
     (y >= 0 ==> -15 <= x - 5 - y <= 25))) --> (* Distribution ==> *)

(x < 0 ==> y <  0 ==> -15 <= 0 + 5 - y <= 25) &&
(x < 0 ==> y >= 0 ==> -15 <= 0 - 5 - y <= 25) &&
(x >= 0 ==> y <  0 ==> -15 <= x + 5 - y <= 25) &&
(x >= 0 ==> y >= 0 ==> -15 <= x - 5 - y <= 25) --> (* Simpl *)

(x < 0 ==> y <  0 ==> -20 <= y <= 20) &&
(x < 0 ==> y >= 0 ==> -20 <= y <= 20) &&
(x >= 0 ==> y <  0 ==> -20 <= x - y <= 20) &&
(x >= 0 ==> y >= 0 ==> -20 <= x - y <= 20) --> (* Simpl *)

A: (x < 0 ==> -20 <= y <= 20) && B: (x >= 0 ==> -20 <= x - y <= 20)
```

We have:

```
requires -5 <= y <= 5 ; 
requires -5 <= x <= 5 ;
```

A is validated:
```
-5 <= y <= 5 ==> (x < 0 ==> -20 <= y <= 20).
```
B is validated:
```
x >= 0 && -5 <= x <= 5 ==> 0 <= x <= 5
0 <= x <= 5 && -5 <= y <= 5 ==> -20 <= x - y <= 20
```