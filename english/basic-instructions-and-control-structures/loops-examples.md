# Examples with read-only arrays

Array is the most common data structure when we are working with loops. It is
then a good example base to exercise with loops, and these examples allow to
rapidly show interesting invariant and will allow us to introduce some
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
also to state that a range of contiguous adresses are valid. It is expressed
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
//                                 THEN the cell "off" in "a" is different of "element"
\forall size_t off ; 0 <= off < length ==> a[off] != element;

// there exists "off" of type "size_t", such that "off" is comprise between 0 and "length"
//                                      AND the cell "off" in "a" equals to "element"
\exists size_t off ; 0 <= off < length && a[off] == element;
*/
```

If we want to sum up the use of these keyword, we would say that on a range of
values, a property is true, either about at least one of them or about all of
them. A common scheme is to constraint this set using another property
(here: `0 <= off < length`) and to prove the actual interesting property on this
smaller set. **But using `exists` and `forall` is fundamentally different**.

With `\forall type a ; p(a) ==> q(a)`, the constraint `p` is followed by an
implication. For all element, if a first property `p` is verified about it, then
we have to verify the second property `q`. If we use a conjunction, as we do for
"exists" (that we will later explain), that would mean that all element verify
both `p` and `q`. Sometimes, it could be what we want to express, but it would
then not correspond anymore to the idea of contraining a set for which we want
to verify some other property.

With `\exists type a ; p(a) && q(a)`, the constraint `p` is followed by a
conjunfction. We say there exists an element such that it satisfies the property
`p` at the same time it also satisfies `q`. If we use an implication, as we do
for "forall", such an expression will always be true if `p` is not a tautologie!
Why? Is there a "a" such that p(a) implies q(a) ? Let us take a "a" such that
p(a) is false, the implication is true.

Cette partie de l'invariant mérite une attention particulière :

```c
//@ loop invariant \forall size_t j; 0 <= j < i ==> array[j] != element;
```

En effet, c'est la partie qui définit l'action de notre boucle, elle indique à
WP ce que la boucle va faire (ou apprendre dans le cas présent) tout au long de
son exécution. Ici en l'occurrence, cette formule nous dit qu'à chaque tour, nous 
savons que pour toute case entre 0 et la prochaine que nous allons visiter (```i``` exclue), elle stocke une valeur différente de l'élément recherché.

Le but de WP associé à la préservation de cet invariant est un peu compliqué, il
n'est pour nous pas très intéressant de se pencher dessus. En revanche, la 
preuve de l'établissement de cet invariant est intéressante :

![But trivial](https://zestedesavoir.com:443/media/galleries/2584/eda30413-2d95-4d0a-ab5c-f36a356ad516.png)

Nous pouvons constater que cette propriété, pourtant complexe, est prouvée par 
Qed sans aucun problème. Si nous regardons sur quelles parties du programme la 
preuve se base, nous pouvons voir l'instruction ```i = 0``` surlignée, et c'est 
bien la dernière instruction que nous effectuons sur ```i``` avant de commencer
la boucle. Et donc effectivement, si nous faisons le remplacement dans la formule 
de l'invariant :

```c
//@ loop invariant \forall size_t j; 0 <= j < 0 ==> array[j] != element;
```

« Pour tout j, supérieur ou égal à 0 et inférieur strict à 0 », cette partie est
nécessairement fausse. Notre implication est donc nécessairement vraie.

# Exemples avec tableaux mutables

Nous allons voir deux exemples avec la manipulation de tableaux en mutation. 
L'un avec une modification totale, l'autre en modification sélective.

## Remise à zéro

Regardons la fonction effectuant la remise à zéro d'un tableau.

```c
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  \forall size_t i; 0 <= i < length ==> array[i] == 0;
*/
void raz(int* array, size_t length){
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

Les seules parties sur lesquelles nous pouvons nous attacher ici sont 
les ```assigns``` de la fonction et de la boucle. À nouveau, nous pouvons
utiliser la notation ```n .. m``` pour indiquer les parties du tableau 
qui sont modifiées.

## Chercher et remplacer

Le dernier exemple qui nous intéresse est l'algorithme « chercher et remplacer ». 
C'est donc un algorithme qui va sélectivement modifier des valeurs dans une 
certaine plage d'adresses. Il est toujours un peu difficile de guider l'outil 
dans ce genre de cas car, d'une part, nous devons garder « en mémoire » ce qui est modifié 
et ce qui ne l'est pas et, d'autre part, parce que l'induction repose sur ce fait.

À titre d'exemple, la première spécification que nous pouvons réaliser pour 
cette fonction ressemblerait à ceci :

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

Nous utilisons la fonction logique ```\at(v, Label)``` qui nous donne la valeur de
la variable `v` au point de programme `Label`. Si nous regardons l'utilisation qui
en est faite ici, nous voyons que dans l'invariant de boucle, nous cherchons à 
établir une relation entre les anciennes valeurs du tableau et leurs potentielles 
nouvelles valeurs :

```c
/*@
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) == old 
                   ==> array[j] == new;
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) != old 
                   ==> array[j] == \at(array[j], Pre);
*/
```

Pour tout élément que nous avons visité, s'il valait la valeur qui doit être
remplacée, alors il vaut la nouvelle valeur, sinon il n'a pas changé. En fait, si nous essayons de prouver l'invariant, WP n'y parvient pas. Dans ce genre de 
cas, le plus simple est encore d'ajouter diverses assertions exprimant les 
propriétés intermédiaires que nous nous attendons à voir facilement prouvées 
et impliquant l'invariant. En fait, nous nous apercevons rapidement que WP 
n'arrive pas à maintenir le fait que nous n'avons pas encore modifié la fin du 
tableau :

```c
for(size_t i = 0; i < length; ++i){
    //@assert array[i] == \at(array[i], Pre); // échec de preuve
    if(array[i] == old) array[i] = new;
}
```

Nous pouvons donc ajouter cette information comme invariant :

```c
/*@
  loop invariant 0 <= i <= length;
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) == old 
                   ==> array[j] == new;
  loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) != old 
                   ==> array[j] == \at(array[j], Pre);

  //La fin du tableau n'a pas été modifiée :
  loop invariant \forall size_t j; i <= j < length
                     ==> array[j] == \at(array[j], Pre);
  loop assigns i, array[0 .. length-1];
  loop variant length-i;
*/
for(size_t i = 0; i < length; ++i){
  if(array[i] == old) array[i] = new;
}
```

Et cette fois, la preuve passera. À noter que si nous tentons la preuve 
directement avec la vérification des RTE, il est possible qu'Alt-Ergo n'y
parvienne pas (CVC4 décharge l'ensemble sans problème). Dans ce cas, nous
pouvons faire séparément les deux preuves (sans, puis avec RTE) ou encore 
ajouter des assertions permettant de guider la preuve dans la boucle :

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

À mesure que nous cherchons à prouver des propriétés plus compliquées et 
notamment dépendantes de boucles, il va y avoir une part de tâtonnement pour
comprendre ce qui manque au prouveur pour réussir la preuve. 

Ce qui peut lui manquer, ce sont des hypothèses. Dans ce type de cas, nous
pouvons tenter d'ajouter des assertions au code pour guider le prouveur. Avec
de l'expérience, nous pouvons regarder le contenu des obligations de preuve ou 
tenter de commencer la preuve avec Coq pour voir si la preuve semble réalisable. 
Parfois le prouveur manque juste de temps, auquel cas, il suffit d'augmenter 
(parfois de beaucoup) la durée du *timeout*. Finalement, la propriété peut 
également être hors de portée du prouveur. Auquel cas, il faudra écrire une
preuve à la main avec un prouveur interactif.

Enfin, il reste le cas où l'implémentation est effectivement fausse, et dans ce
cas, il faut la corriger. Et c'est là que nous utiliserons plutôt le test que la
preuve, car le test permet de prouver la présence d'un bug. ;)