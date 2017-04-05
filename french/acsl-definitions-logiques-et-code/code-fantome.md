Derrière ce titre faisant penser à un scénario de film d'action se cache en fait
un moyen d'enrichir la spécification avec des informations sous la forme de code
en langage C. Ici, l'idée va être d'ajouter des variables et du code source qui
n'interviendra pas dans le programme réel mais permettant de créer des états 
logiques qui ne seront visibles que depuis la preuve. Par cet intermédiaire, 
nous pouvons rendre explicites des propriétés logiques qui étaient auparavant
implicites.

# Syntaxe

Le code fantôme est ajouté par l'intermédiaire d'annotations qui vont contenir 
du code C ainsi que la mention ```ghost```. 

```c
/*@
  ghost
  // code en langage C
*/
```

Les seules règles que nous devons respecter dans un tel code est que nous ne 
devons jamais écrire une portion de mémoire qui n'est pas elle-même définie dans
du code fantôme et que le code en question doit terminer tout bloc qu'il ouvrirait.
Mis à par cela, tout calcul peut être inséré tant qu'il n'écrit pas la mémoire. 

Voici quelques exemples pour la syntaxe de code fantôme :

```c
//@ ghost int ghost_glob_var = 0;

void foo(int a){
  //@ ghost int ghost_loc_var = a;

  //@ ghost Ghost_label: ;
  a = 28 ;

  //@ ghost if(a < 0){ ghost_loc_var = 0; }

  //@ assert ghost_loc_var == \at(a, Ghost_label) == \at(a, Pre);
}
```

Il faut être très prudent lorsque nous produisons ce genre de code. En effet, 
aucune vérification n'est effectuée pour s'assurer que nous n'écrivons pas dans
la mémoire globale par erreur. Ce problème étant comme la vérification elle-même, 
un problème indécidable, une telle analyse serait un travail de preuve à part 
entière. Par exemple, ce code est accepté en entrée de Frama-C, alors qu'il 
modifie manifestement l'état de la mémoire du programme :

```c
int a;

void foo(){
  //@ ghost a = 42;
}
```

Il faut donc faire très attention à ce que nous faisons avec du code fantôme.

# Expliciter un état logique

Le but du code ghost est de rendre explicite des informations généralement 
implicites. Par exemple, dans la section précédente, nous nous en sommes servi
pour récupérer explicitement un état logique connu à un point de programme 
donné. 

Prenons maintenant un exemple plus poussé. Nous voulons par exemple prouver que
la fonction suivante nous retourne la valeur maximale des sommes de sous 
tableaux possibles d'un tableau donné. Un sous-tableau d'un tableau "a" est un
sous-ensemble contigu de valeur de "a". Par exemple, pour un tableau ```{ 0 , 3 , -1 , 4 }```,
des exemples de sous tableaux peuvent être ```{}```, ```{ 0 }```, ```{ 3 , -1 }```
, ```{ 0 , 3 , -1 , 4 }```, ... Notez que comme nous autorisons le tableau vide,
la somme est toujours au moins égale à 0. Dans le tableau précédent, le sous 
tableau de valeur maximale est ```{ 3 , -1 , 4 }```, la fonction renverra donc 6.

```c
int max_subarray(int *a, size_t len) {
  int max = 0;
  int cur = 0;
  for(size_t i = 0; i < len; i++) {
    cur += a[i];
    if (cur < 0)   cur = 0;
    if (cur > max) max = cur;
  }
  return max;
}
```

Pour spécifier la fonction précédente, nous allons avoir besoin d'exprimer 
axiomatiquement la somme. Ce n'est pas très complexe, et le lecteur pourra
s'exercer en exprimant les axiomes nécessaires au bon fonctionnement de cette 
axiomatique :

```c
/*@ axiomatic Sum {
  logic integer sum(int *array, integer begin, integer end) reads a[begin..(end-1)];
}*/
```

La correction est caché ici :

[[secret]]
| ```c
| /*@
|   axiomatic Sum_array{
|     logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
|    
|     axiom empty: 
|       \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
|     axiom range:
|       \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1)+a[e-1];
|   }
| */
| ```

La spécification de notre fonction est la suivante :

```c
/*@ 
  requires \valid(a+(0..len-1));
  assigns \nothing;
  ensures \forall integer l, h;  0 <= l <= h <= len ==> sum(a,l,h) <= \result;
  ensures \exists integer l, h;  0 <= l <= h <= len &&  sum(a,l,h) == \result;
*/
```

Pour toute paire de bornes la valeur retournée doit être supérieure ou égale
et il doit exister une paire telle que c'est égal. Par rapport à cette spécification,
si nous devons ajouter les invariants de boucles, nous nous apercevons rapidement 
qu'il va nous manquer des informations. Nous avons besoin d'exprimer ce que sont
les valeurs ```max``` et ```cur``` et quelles relations il existe entre elles,
mais rien ne nous le permet !

En substance, notre post-condition a besoin de savoir qu'il existe des 
bornes ```low``` et ```high``` telles que la somme calculée correspond à ces bornes. 
Or notre code, n'exprime rien de tel d'un point de vue logique et rien ne nous 
permet *a priori* de faire cette liaison en utilisant des formulations logiques.
Nous allons donc utiliser du code ghost pour conserver ces bornes et exprimer 
l'invariant de notre boucle.

Nous allons d'abord avoir besoin de 2 variables qui vont nous permettre de stocker
les valeurs des bornes de la plage maximum, nous les appellerons ```low``` 
et ```high```. Chaque fois que nous trouverons une plage où la somme est plus 
élevée nous le mettrons à jour. Ces bornes correspondront donc à la somme indiquée
par ```max```. Cela induit que nous avons encore besoin d'une autre paire de 
bornes : celle correspondant à la variable de somme ```cur``` à partir de laquelle 
nous pourrons construire les bornes de ```max```. Pour celle-ci, nous n'avons 
besoin que d'ajouter une variable ghost : le minimum actuel ```cur_low```, la 
borne supérieure de la somme actuelle étant indiquée par la variable ```i``` de la 
boucle.

```c
/*@ 
  requires \valid(a+(0..len-1));
  assigns \nothing;
  ensures \forall integer l, h;  0 <= l <= h <= len ==> sum(a,l,h) <= \result;
  ensures \exists integer l, h;  0 <= l <= h <= len &&  sum(a,l,h) == \result;
*/
int max_subarray(int *a, size_t len) {
  int max = 0;
  int cur = 0;
  //@ ghost size_t cur_low = 0; 
  //@ ghost size_t low = 0;
  //@ ghost size_t high = 0; 

  /*@ 
    loop invariant BOUNDS: low <= high <= i <= len && cur_low <= i;
    
    loop invariant REL :   cur == sum(a,cur_low,i) <= max == sum(a,low,high);
    loop invariant POST:   \forall integer l;    0 <= l <= i      ==> sum(a,l,i) <= cur;
    loop invariant POST:   \forall integer l, h; 0 <= l <= h <= i ==> sum(a,l,h) <= max;
   
    loop assigns i, cur, max, cur_low, low, high;
    loop variant len - i; 
  */
  for(size_t i = 0; i < len; i++) {
    cur += a[i];
    if (cur < 0) {
      cur = 0;
      /*@ ghost cur_low = i+1; */
    }
    if (cur > max) {
      max = cur;
      /*@ ghost low = cur_low; */
      /*@ ghost high = i+1; */
    }
  }
  return max;
}
```

L'invariant ```BOUNDS``` exprime comment sont ordonnées les différentes bornes 
pendant le calcul. L'invariant ```REL``` exprime ce que signifient les 
valeurs ```cur``` et ```max``` par rapport à ces bornes. Finalement, 
l'invariant ```POST``` permet de faire le lien entre les invariants précédents 
et la post-condition de la fonction.

Le lecteur pourra vérifier que cette fonction est effectivement prouvée sans la
vérification des RTE. Si nous ajoutons également le contrôle des RTE, nous pouvons
voir que le calcul de la somme indique un dépassement possible sur les entiers.

Ici, nous ne chercherons pas à le corriger car ce n'est pas l'objet de l'exemple.
Le moyen de prouver cela dépend en fait fortement du contexte dans lequel on 
utilise la fonction. Une possibilité est de restreindre fortement le contrat en
imposant des propriétés à propos des valeurs et de la taille du tableau. Par 
exemple : nous pourrions imposer une taille maximale et des bornes fortes pour
chacune des cellules. Une autre possibilité est d'ajouter une valeur d'erreur
en cas de dépassement (par exemple $-1$), et de spécifier qu'en cas de 
dépassement, c'est cette valeur qui est renvoyée.