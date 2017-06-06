# Correctly write what we expect

This is certainly the hardest part of our work. Programming is already an effort
that consists in writing algorithms that correctly respond to our need. 
Specifying request the same kind of work, except that we do not try to precise
*how* we respond to the need but *what* is exactly our need. To prove that our
code implements what we need, we must be able to describe exactly what we need.

From now, we will use an other example with the `max` function:

```c
int max(int a, int b){
  return (a > b) ? a : b;
}
```

The reader could write and prove their own specification. We will start using
this one:

```c
/*@
  ensures \result >= a && \result >= b;
*/
int max(int a, int b){
  return (a > b) ? a : b;
}
```

If we ask WP to prove this code, it will succeed without any problem. However,
is our specification really correct ? We can try to prove this calling code:

```c
void foo(){
  int a = 42;
  int b = 37;
  int c = max(a,b);

  //@assert c == 42;
}
```

There, it will fail. In fact, we can go further by modifying the body of the
`max` function and notice that the following code is also correct with respect
to the specification:

```c
#include <limits.h>

/*@
  ensures \result >= a && \result >= b;
*/
int max(int a, int b){
  return INT_MAX;
}
```

Our specification is too much permissive. We have to be more precise. We
expect the result, not only to be greater or equal to both parameters, but
also that the result is one of them:

```c
/*@
  ensures \result >= a && \result >= b;
  ensures \result == a || \result == b;
*/
int max(int a, int b){
  return (a > b) ? a : b;
}
```

# Pointers

If there is one notion that we permently have to confront with in C language,
this is definitely the notion of pointer. Pointers are quite hard to
manipulate correctly, and they still are the main source of critical bugs in
programs, so they benefit of a preferential treatment in ACSL.

We can illustrate with a swap function for C integers:

```c
/*@
  ensures *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
```

## History of values

Here, we introduce a first logic builtin function of ACSL: `old`, that allows
us to get the old value of a given element. So, our specification defines
that the function must ensure that after the call, the value of `a` is the
old (that is to say, before the call) value of `b` and conversely.

The '\old` function can only be used in the post-condition of a function. If
we need this type of information somewhere else, we will use `at` that allows
us to express that we want the value of a variable at a particular program
point. This function recieves two parameters. The first one is the variable
(or memory location) for which we want to get its value and the second one is
the program point (as a C label) that we want to consider.

For example, we could write:

```c
  int a = 42;
 Label_a:
  a = 45;

  //@assert a == 45 && \at(a, Label_a) == 42;
```

Of course, we can use any C label in our code, but we also have 6 builtins
labels defined by ACSL that can be used, however WP does not support all
of them currently:

- ```Pre```/```Old``` : value before function call,
- ```Post``` : value after function call,
- ```LoopEntry``` : value at loop entry (not supported yet),
- ```LoopCurrent``` : value at the beginning of the current step of the loop
  (not supported yet),
- ```Here``` : value at the current program point.

[[information]]
| The behavior of `Here` is in fact the default behavior when we consider a
| variable. Its use with `at` with generally let us ensure that what we write
| is not ambigous, and is more readable, when we express properties about
| values at different program points in the same expression.

Whereas `\old` can only be used in function post-conditions, `\at` can be used
anywhere. However, we cannot use any program point with respect to the type
annotation we are writing. `Old` and `Post` are only available in function
post-conditions, `Pre` and `Here` are available everywhere. `LoopEntry` and
`LoopCurrent` are only available in the context of loops (which we will detail
later in this tutorial).

For the moment, we will not need `\at` but it can often be useful, if not
essential, when we want to make our specification precise.

## Pointers validity

If we try to prove that the swap function is correct (comprising RTE
verification), our post-condition is indeed verified but WP failed to prove
some possibilities of runtime-error, since we perform access to some pointers
that we did not indicate to be valid pointers in the precondition of the
function.

We can express that the dereferencing of a pointer is valid using the `\valid`
predicate of ACSL which recieves the pointer in input:

```c
/*@
  requires \valid(a) && \valid(b);
  ensures  *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
```

Once we have specified that the pointers we recieve in input are valid,
dereferencing is assured to not produce undefined behaviors.

As we will see later in this tutorial, `\valid` can take more than one pointer
in parameter. For example, we can give it an expression such as:
`valid(p + (s .. e))` which means "forall `i` between included `s` and `e`, 
`p+i` is a valid pointer. This kind of expression will be extremely useful
when we will specify properties about arrays in specifications.

Si nous nous intéressons aux assertions ajoutées par WP dans la fonction swap
avec la validation des RTEs, nous pouvons constater qu'il existe une variante
de ```\valid``` sous le nom ```\valid_read```. Contrairement au premier, 
celui-ci assure que le pointeur peut être déréférencé mais en lecture 
seulement. Cette subtilité est due au fait qu'en C, le downcast de pointeur 
vers un élément const est très facile à faire mais n'est pas forcément légal.

Typiquement, dans le code suivant :

```c
/*@ requires \valid(p); */
int unref(int* p){
  return *p;
}

int const value = 42;

int main(){
  int i = unref(&value);
}
```

Le déréférencement de ```p``` est valide, pourtant la pré-condition de ```unref```
ne sera pas validée par WP car le déréférencement de l'adresse de ```value``` 
n'est légal qu'en lecture. Un accès en écriture sera un comportement 
indéterminé. Dans un tel cas, nous pouvons préciser que dans ```unref```, le 
pointeur ```p``` doit être nécessairement ```\valid_read``` et pas ```\valid```.

## Effets de bord

Notre fonction ```swap``` est bien prouvable au regard de sa spécification et
de ses potentielles erreurs à l'exécution, mais est-elle pour autant 
suffisamment spécifiée ? Pour voir cela, nous pouvons modifier légèrement le code
de cette façon (nous utilisons ```assert``` pour analyser des propriétés 
ponctuelles) :

```c
int h = 42; //nous ajoutons une variable globale

/*@
  requires \valid(a) && \valid(b);
  ensures  *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

int main(){
  int a = 37;
  int b = 91;

  //@ assert h == 42;
  swap(&a, &b);
  //@ assert h == 42;
}
```
Le résultat n'est pas vraiment celui escompté :

![Échec de preuve sur une globale non concernée par l'appel à ```swap```](https://zestedesavoir.com:443/media/galleries/2584/1aeddaba-4761-4d30-b499-b99f8815a6da.png)

En effet, nous n'avons pas spécifié les effets de bords autorisés pour notre
fonction. Pour spécifier les effets de bords, nous utilisons la clause ```assigns```
qui fait partie des post-conditions de la fonction. Elle nous permet de spécifier 
quels éléments **non locaux** (on vérifie bien des effets de bord), sont 
susceptibles d'être modifiés par la fonction.

Par défaut, WP considère qu'une fonction a le droit de modifier n'importe quel
élément en mémoire. Nous devons donc préciser ce qu'une fonction est en droit 
de modifier. Par exemple pour la fonction swap :

```c
/*@
  requires \valid(a) && \valid(b);
 
  assigns *a, *b;

  ensures  *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
```

Si nous rejouons la preuve avec cette spécification, la fonction et les 
assertions que nous avions demandées dans le main seront validées par WP.

Finalement, il peut arriver que nous voulions spécifier qu'une fonction ne 
provoque pas d'effets de bords. Ce cas est précisé en donnant ```\nothing```
à ```assigns``` :

```c
/*@
  requires \valid_read(a) && \valid_read(b);

  assigns  \nothing;

  ensures \result == *a || \result == *b;
  ensures \result >= *a && \result >= *b;
*/
int max_ptr(int* a, int* b){
  return (*a > *b) ? *a : *b ;
}
```
Le lecteur pourra maintenant reprendre les exemples précédents y intégrer 
la bonne clause ```assigns``` ;) .

## Séparation des zones de la mémoire

Les pointeurs apportent le risque d'aliasing (plusieurs pointeurs ayant accès à
la même zone de mémoire). Si dans certaines fonctions, cela ne pose pas de 
problème, par exemple dans le cas où nous passons les deux mêmes pointeurs
à notre fonction ```swap``` où la spécification est toujours vérifiée par le 
code source. Dans d'autre cas, ce n'est pas si simple :

```c
#include <limits.h>

/*@
  requires \valid(a) && \valid_read(b);
  assigns  *a;
  ensures  *a == \old(*a)+ *b;
  ensures  *b == \old(*b);
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
```

Si nous demandons à WP de prouver cette fonction, nous obtenons le 
résultat suivant :

![Échec de preuve : risque d'aliasing](https://zestedesavoir.com:443/media/galleries/2584/9cd9f343-986a-4271-95a7-a35df114d8bd.png)

La raison est simplement que rien ne garantit que le pointeur ```a``` est bien
différent du pointeur ```b```. Or, si les pointeurs sont égaux,

- la propriété ```*a == \old(*a) + *b``` signifie en fait 
   ```*a == \old(*a) + *a```, ce ne peut être vrai que si l'ancienne valeur 
   pointée par ```a``` était 0, ce qu'on ne sait pas,
- la propriété ```*b == \old(*b)``` n'est pas validée car potentiellement,
  nous la modifions.

[[question]]
| Pourquoi la clause assign est-elle validée ?
|
| C'est simplement dû au fait, qu'il n'y a bien que la zone mémoire pointée par
| ```a``` qui est modifiée étant donné que si ```a != b``` nous ne modifions bien 
| que cette zone et que si ```a == b```, il n'y a toujours que cette zone, et 
| pas une autre.

Pour assurer que les pointeurs sont bien sur des zones séparées de mémoire, 
ACSL nous offre le prédicat ```\separated(p1, ..., pn)``` qui reçoit en entrée 
un certain nombre de pointeurs et qui va nous assurer qu'ils sont deux à deux 
disjoints. Ici, nous spécifierions :

```c
#include <limits.h>

/*@
  requires \valid(a) && \valid_read(b);
  requires \separated(a, b);
  assigns  *a;
  ensures  *a == \old(*a)+ *b;
  ensures  *b == \old(*b);
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
```

Et cette fois, la preuve est effectuée :

![Résolution des problèmes d'aliasing](https://zestedesavoir.com:443/media/galleries/2584/dcca986e-e819-4320-a481-7c924635f8bb.png)

Nous pouvons noter que nous ne nous intéressons pas ici à la preuve de 
l'absence d'erreur à l'exécution car ce n'est pas l'objet de cette section.
Cependant, si cette fonction faisait partie d'un programme complet à vérifier,
il faudrait définir le contexte dans lequel on souhaite l'utiliser et définir
les pré-conditions qui nous garantissent l'absence de débordement en conséquence.