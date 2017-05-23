Les axiomes sont des propriétés dont nous énonçons qu'elles sont vraies quelle 
que soit la situation. C'est un moyen très pratique d'énoncer des notions 
complexes qui vont pouvoir rendre le processus très efficace en abstrayant 
justement cette complexité. Évidemment, comme toute propriété exprimée comme un
axiome est supposée vraie, il faut également faire très attention à ce que nous
définissons car si nous introduisons une propriété fausse dans les notions que 
nous supposons vraies alors ... nous saurons tout prouver, même ce qui est faux.

# Syntaxe

Pour introduire une définition axiomatique, nous utilisons la syntaxe suivante :

```c
/*@
  axiomatic Name_of_the_axiomatic_definition {
    // ici nous pouvons définir ou déclarer des fonctions et prédicats

    axiom axiom_name { Label0, ..., LabelN }:
      // property ;

    axiom other_axiom_name { Label0, ..., LabelM }:
      // property ;

    // ... nous pouvons en mettre autant que nous voulons
  }
*/
```

Nous pouvons par exemple définir cette axiomatique :

```c
/*@
  axiomatic lt_plus_lt{
    axiom always_true_lt_plus_lt:
      \forall integer i, j; i < j ==> i+1 < j+1 ;
  }
*/
```

Et nous pouvons voir que dans Frama-C, la propriété est bien supposée vraie :

![Premier axiome, supposé vrai par Frama-C](/media/galleries/2584/8cd93c4d-dead-4fa9-a4ba-d9759d0e8bde.png)

[[secret]]
| Actuellement nos prouveurs automatiques n'ont pas la puissance nécessaire
| pour calculer *la réponse à la grande question sur la vie, l'univers et le 
| reste*. Qu'à cela ne tienne nous pouvons l'énoncer comme axiome ! Reste à
| comprendre la question pour savoir où ce résultat peut-être utile ...
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

## Lien avec la notion de lemme

Les lemmes et les axiomes vont nous permettre d'exprimer les mêmes types de 
propriétés, à savoir des propriétés exprimées sur des variables quantifiées (et
éventuellement des variables globales, mais cela reste assez rare puisqu'il est
difficile de trouver une propriété qui soit globalement vraie à leur sujet tout
en étant intéressante). Outre ce point commun, il faut également savoir que 
comme les axiomes, en dehors de leur définition, les lemmes sont considérés 
vrais par WP. 

La seule différence entre lemme et axiome du point de vue de la preuve est donc
que nous devrons fournir une preuve que le premier est valide alors que l'axiome
est toujours supposé vrai.

# Définition de fonctions ou prédicats récursifs

Les définitions axiomatiques de fonctions ou de prédicats récursifs sont 
particulièrement utiles car elles vont permettre d'empêcher les prouveurs de 
dérouler la récursion quand c'est possible, notamment parce que justement, à la
manière dont nous avions ajouté un lemme sur la factorielle nous allons pouvoir
directement exprimer l'induction dans l'axiomatique.

L'idée est alors de ne pas définir directement la fonction ou le prédicat mais 
plutôt de la déclarer puis de définir des axiomes spécifiant son comportement.
Si nous reprenons par exemple la factorielle, nous pouvons la définir 
axiomatiquement de cette manière :

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

Dans cette définition axiomatique, notre fonction n'a pas de corps. Son 
comportement étant défini par les axiomes ensuite définis. Une petite subtilité
est qu'il faut prendre garde au fait que si les axiomes énoncent des propriétés
à propos du contenu d'une ou plusieurs zones mémoires pointées, il faut 
spécifier ces zones mémoires en utilisant la notation ```reads``` au niveau de
la déclaration. Si nous oublions une telle spécification, le prédicat, ou la 
fonction, sera considéré comme énoncé à propos du pointeur et non à propos de la
zone mémoire pointée. Une modification de celle-ci n'entraînera donc pas 
l'invalidation d'une propriété connue axiomatiquement.

Si par exemple, nous voulons définir qu'un tableau ne contient que des 0, nous
pouvons le faire de cette façon :

```c
/*@
  axiomatic A_all_zeros{
    predicate zeroed{L}(int* a, integer b, integer e) reads a[b .. e-1];

    axiom zeroed_empty{L}:
      \forall int* a, integer b, e; b >= e ==> zeroed{L}(a,b,e);

    axiom zeroed_range{L}:
      \forall int* a, integer b, e; b < e+1 ==>
        zeroed{L}(a,b,e+1) <==> (zeroed{L}(a,b,e) && a[e] == 0);
  }
*/
```

Et nous pouvons à nouveau prouver notre fonction de remise à zéro avec cette
nouvelle définition :

```c
#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  zeroed(array,0,length);
*/
void raz(int* array, size_t length){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant zeroed(array,0,i);
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    array[i] = 0;
}
```

Selon votre version de Frama-C et de vos prouveurs automatiques, la preuve de 
préservation de l'invariant peut échouer. Une raison à cela est que le prouveur ne
parvient pas à garder l'information que ce qui précède la cellule en cours de
traitement par la boucle est toujours à 0. Nous pouvons ajouter un lemme dans
notre base de connaissance, expliquant que si l'ensemble des valeurs d'un tableau
n'a pas changé, alors la propriété est toujours vérifiée :

```c
/*@
  predicate same_elems{L1,L2}(int* a, integer b, integer e) =
    \forall integer i; b <= i < e ==> \at(a[i],L1) == \at(a[i],L2);

  lemma no_changes{L1,L2}:
  \forall int* a, integer b, e;
  same_elems{L1,L2}(a,b,e) ==> zeroed{L1}(a,b,e) ==> zeroed{L2}(a,b,e);
*/
```

Et d'énoncer une assertion pour spécifier ce qui n'a pas changé entre le début 
du bloc de la boucle (marqué par le *label* `L` dans le code) et la fin (qui se
trouve être `Here` puisque nous posons notre assertion à la fin) :

```c
for(size_t i = 0; i < length; ++i){
  L:
  array[i] = 0;
  //@ assert same_elems{L,Here}(array,0,i);
}
```

À noter que dans cette nouvelle version du code, la propriété énoncée par notre
lemme n'est pas prouvée par les solveurs automatiques, qui ne savent pas raisonner
pas induction. Pour les curieux, la (très simple) preuve en Coq est ci-dessous :

[[secret]]
| ```coq
| (* Généré par WP *)
| Definition P_same_elems (Mint_0 : farray addr Z) (Mint_1 : farray addr Z)
|     (a : addr) (b : Z) (e : Z) : Prop :=
|     forall (i : Z), let a_1 := (shift_sint32 a i%Z) in ((b <= i)%Z) ->
|       ((i < e)%Z) -> (((Mint_0.[ a_1 ]) = (Mint_1.[ a_1 ]))%Z).
| Goal
|   forall (i_1 i : Z), forall (t_1 t : farray addr Z), forall (a : addr),
|     ((P_zeroed t a i_1%Z i%Z)) -> ((P_same_elems t_1 t a i_1%Z i%Z)) -> ((P_zeroed t_1 a i_1%Z i%Z)).
| (* Notre preuve *)
| Proof.
|   intros b e.
|   (* par induction sur la distance entre b et e *)
|   induction e using Z_induction with (m := b) ; intros mem_l2 mem_l1 a Hz_l1 Hsame.
|   (* cas de base : Axiome "empty" *)
|   + apply A_A_all_zeros.Q_zeroed_empty ; assumption.
|   + replace (e + 1) with (1 + e) in * ; try omega.
|     (* on utilise l'axiome range *)
|     rewrite A_A_all_zeros.Q_zeroed_range in * ; intros Hinf.
|     apply Hz_l1 in Hinf ; clear Hz_l1 ; inversion_clear Hinf as [Hlast Hothers].
|     split.
|     (* sous plage de Hsame *)
|     - rewrite Hsame ; try assumption ; omega.
|     (* hypothèse d'induction *)
|     - apply IHe with (t := mem_l1) ; try assumption.
|       * unfold P_same_elems ; intros ; apply Hsame ; omega.
| Qed.
| ```

Dans le cas présent, utiliser une axiomatique est contre-productif : notre
propriété est très facilement exprimable en logique du premier ordre comme
nous l'avons déjà fait précédemment. Les axiomatiques sont faites pour écrire
des définitions qui ne sont pas simples à exprimer dans le formalisme de base
d'ACSL. Mais il est mieux de commencer avec un exemple facile à lire. 

# Consistance

En ajoutant des axiomes à notre base de connaissances, nous pouvons produire des
preuves plus complexes car certaines parties de cette preuve, mentionnées par 
les axiomes, ne nécessiteront plus de preuves qui allongeraient le processus 
complet. Seulement, en faisant cela **nous devons être extrêmement prudents**.
En effet, la moindre hypothèse fausse introduite dans la base pourraient rendre
tous nos raisonnements futiles. Notre raisonnement serait toujours correct, mais
basé sur des connaissances fausses, il ne nous apprendrait donc plus rien de correct.

L'exemple le plus simple à produire est le suivant:

```c
/*@
  axiomatic False{
    axiom false_is_true: \false;
  }
*/

int main(){
  // Exemples de propriétés prouvées

  //@ assert \false;
  //@ assert \forall integer x; x > x;
  //@ assert \forall integer x,y,z ; x == y == z == 42;
  return *(int*) 0;
}
```

Et tout est prouvé, y compris que le déréférencement de l'adresse 0 est OK :

![Preuve de tout un tas de choses fausses](https://zestedesavoir.com:443/media/galleries/2584/8bb12c3f-5da7-4f44-a889-fa5df0ab8e7a.png)

Évidemment cet exemple est extrême, nous n'écririons pas un tel axiome. Le
problème est qu'il est très facile d'écrire une axiomatique subtilement fausse
lorsque nous exprimons des propriétés plus complexes, ou que nous commençons à
poser des suppositions sur l'état global d'un système. 

Quand nous commençons à créer de telles définitions, ajouter de temps en 
temps une preuve ponctuelle de « *false* » dont nous voulons qu'elle échoue permet 
de s'assurer que notre définition n'est pas inconsistante. Mais cela ne fait pas 
tout ! Si la subtilité qui crée le comportement faux est suffisamment cachée, les
prouveurs peuvent avoir besoin de beaucoup d'informations autre que l'axiomatique
elle-même pour être menés jusqu'à l'inconsistance, donc il faut toujours être 
vigilant !

Notamment parce que par exemple, la mention des valeurs lues par une fonction
ou un prédicat défini axiomatiquement est également importante pour la 
consistance de l'axiomatique. En effet, comme mentionné précédemment, si nous
n'exprimons pas les valeurs lues dans le cas de l'usage d'un pointeur, la 
modification d'une valeur du tableau n'invalide pas une propriété que l'on 
connaitrait à propos du contenu du tableau par exemple. Dans un tel cas, la 
preuve passe mais l'axiome n'exprimant pas le contenu, nous ne prouvons rien.

Par exemple, si nous reprenons l'exemple de mise à zéro, nous pouvons modifier
la définition de notre axiomatique en retirant la mention des valeurs dont 
dépendent le prédicat : ```reads a[b .. e-1]```. La preuve passera toujours
mais n'exprimera plus rien à propos du contenu des tableaux considérés.

# Exemple : comptage de valeurs

Dans cet exemple, nous cherchons à prouver qu'un algorithme compte bien les 
occurrences d'une valeur dans un tableau. Nous commençons par définir 
axiomatiquement la notion de comptage dans un tableau :

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
        (from < to+1 && in[to] == v) ==>
	  l_occurrences_of(v,in,from,to+1) == 1+l_occurrences_of(v,in,from,to);

    axiom occurrences_positive_range_without_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to+1 && in[to] != v) ==>
	  l_occurrences_of(v,in,from,to+1) == l_occurrences_of(v,in,from,to);
  }
*/
```

Nous avons trois cas à gérer : 

- la plage de valeur concernée est vide : le nombre d'occurrences est 0 ;
- la plage de valeur n'est pas vide et le dernier élément est celui recherché :
  le nombre d'occurrences est : le nombre d'occurrences dans la plage actuelle que
  l'on prive du dernier élément, plus 1 ;
- la plage de valeur n'est pas vide et le dernier élément n'est pas celui 
  recherché : le nombre d'occurrences est le nombre d'occurrences dans la plage
  privée du dernier élément.

Par la suite, nous pouvons écrire la fonction C exprimant ce comportement et la
prouver :

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

Une alternative au fait de spécifier que dans ce code ```result``` est au 
maximum ```i``` est d'exprimer un lemme plus général à propos de la valeur
du nombre d'occurrences, dont nous savons qu'elle est comprise entre 0 et 
la taille maximale de la plage de valeurs considérée :

```c
/*@
lemma l_occurrences_of_range{L}:
  \forall int v, int* array, integer from, to:
    from <= to ==> 0 <= l_occurrences_of(v, a, from, to) <= to-from;
*/
```

La preuve de ce lemme ne pourra pas être déchargée par un solveur automatique. Il
faudra faire cette preuve interactivement avec Coq par exemple. Exprimer des 
lemmes généraux prouvés manuellement est souvent une bonne manière d'ajouter des
outils aux prouveurs pour manipuler plus efficacement les axiomatiques, sans 
ajouter formellement d'axiomes qui augmenteraient nos chances d'introduire des
erreurs. Ici, nous devrons quand même réaliser les preuves des propriétés 
mentionnées.

# Exemple : le tri

Nous allons prouver un simple tri par sélection :

```c
size_t min_idx_in(int* a, size_t beg, size_t end){
  size_t min_i = beg;
  for(size_t i = beg+1; i < end; ++i)
    if(a[i] < a[min_i]) min_i = i;
  return min_i;
}

void swap(int* p, int* q){
  int tmp = *p; *p = *q; *q = tmp;
}

void sort(int* a, size_t beg, size_t end){
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}
```

Le lecteur pourra s'exercer en spécifiant et en prouvant les fonctions de 
recherche de minimum et d'échange de valeur. Nous cachons la correction 
ci-dessous et allons nous concentrer plutôt sur la spécification et la preuve de
la fonction de tri qui sont une illustration intéressant de l'usage des
axiomatiques.

[[secret]]
| ```c
| /*@
|   requires \valid_read(a + (beg .. end-1));
|   requires beg < end;
| 
|   assigns  \nothing;
| 
|   ensures  \forall integer i; beg <= i < end ==> a[\result] <= a[i];
|   ensures  beg <= \result < end;
| */
| size_t min_idx_in(int* a, size_t beg, size_t end){
|   size_t min_i = beg;
| 
|   /*@
|     loop invariant beg <= min_i < i <= end;
|     loop invariant \forall integer j; beg <= j < i ==> a[min_i] <= a[j];
|     loop assigns min_i, i;
|     loop variant end-i;
|   */
|   for(size_t i = beg+1; i < end; ++i){
|     if(a[i] < a[min_i]) min_i = i;
|   }
|   return min_i;
| }
| 
| /*@
|   requires \valid(p) && \valid(q);
|   assigns  *p, *q;
|   ensures  *p == \old(*q) && *q == \old(*p);
| */
| void swap(int* p, int* q){
|   int tmp = *p; *p = *q; *q = tmp;
| }
| ```
 
En effet, une erreur commune que nous pourrions faire dans le cas de la preuve 
du tri est de poser cette spécification (qui est vraie !) :

```c
/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

/*@
  requires \valid(a + (beg .. end-1));
  requires beg < end;
  assigns  a[beg .. end-1];
  ensures sorted(a, beg, end);
*/
void sort(int* a, size_t beg, size_t end){
  /*@ //annotation de l'invariant */
  for(size_t i = beg ; i < end ; ++i){
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
  }
}
```

**Cette spécification est vraie**. Mais si nous nous rappelons la 
partie concernant les spécifications, nous nous devons d'exprimer précisément ce
que nous attendons. Avec la spécification actuelle, nous ne prouvons pas toutes
les propriétés nécessaires d'un tri ! Par exemple, cette fonction remplit 
pleinement la spécification :

```c
/*@
  requires \valid(a + (beg .. end-1));
  requires beg < end;

  assigns  a[beg .. end-1];
  
  ensures sorted(a, beg, end);
*/
void fail_sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant \forall integer j; beg <= j < i ==> a[j] == 0;
    loop assigns i, a[beg .. end-1];
    loop variant end-i;
  */
  for(size_t i = beg ; i < end ; ++i)
    a[i] = 0;
}
```

En fait, notre spécification oublie que tous les éléments qui étaient 
originellement présents dans le tableau à l'appel de la fonction doivent
toujours être présents après l'exécution de notre fonction de tri. Dit
autrement, notre fonction doit en fait produire la permutation triée des
valeurs du tableau. 

Une propriété comme la définition de ce qu'est une permutation s'exprime 
extrêmement bien par l'utilisation d'une axiomatique. En effet, pour déterminer
qu'un tableau est la permutation d'un autre, les cas sont très limités. 
Premièrement, le tableau est une permutation de lui-même, puis l'échange de
deux valeurs sans changer les autres est également une permutation, et 
finalement si nous créons la permutation $p_2$ d'une permutation $p_1$, puis que 
nous créons la permutation $p_3$ de $p_2$, alors par transitivité $p_3$ est une
permutation de $p_1$.

Ceci est exprimé par le code suivant :

```c
/*@
  predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) && \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==> \at(a[k], L1) == \at(a[k], L2);

  axiomatic Permutation{
    predicate permutation{L1,L2}(int* a, integer b, integer e)
     reads \at(*(a+(b .. e - 1)), L1), \at(*(a+(b .. e - 1)), L2);

    axiom reflexive{L1}: 
      \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);

    axiom swap{L1,L2}:
      \forall int* a, integer b,e,i,j ;
        swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);
	
    axiom transitive{L1,L2,L3}:
      \forall int* a, integer b,e ; 
        permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==> permutation{L1,L3}(a, b, e);
  }
*/
```

Nous spécifions alors que notre tri nous crée la permutation triée du tableau
d'origine et nous pouvons prouver l'ensemble en complétant l'invariant de la
fonction :

```c
/*@
  requires beg < end && \valid(a + (beg .. end-1));
  assigns  a[beg .. end-1];  
  ensures sorted(a, beg, end);
  ensures permutation{Pre, Post}(a,beg,end);
*/
void sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end;
    loop invariant sorted(a, beg, i) && permutation{Begin, Here}(a, beg, end);
    loop invariant \forall integer j,k; beg <= j < i ==> i <= k < end ==> a[j] <= a[k];
    loop assigns i, a[beg .. end-1];
    loop variant end-i;
  */
  for(size_t i = beg ; i < end ; ++i){
    //@ ghost begin: ;
    size_t imin = min_idx_in(a, i, end);
    swap(&a[i], &a[imin]);
    //@ assert swap_in_array{begin,Here}(a,beg,end,i,imin);
  }
}
```

Cette fois, notre propriété est précisément définie, la preuve reste assez
simple à faire passer, ne nécessitant que l'ajout d'une assertion que le bloc
de la fonction n'effectue qu'un échange des valeurs dans le tableau (et donnant
ainsi la transition vers la permutation suivante du tableau). Pour définir cette
notion d'échange, nous utilisons une annotation particulière (à la ligne 16),
introduite par le mot-clé ```ghost```. Ici, le but est d'introduire un *label* 
fictif dans le code qui est uniquement visible d'un point de vue spécification.
C'est l'objet de la prochaine section.
