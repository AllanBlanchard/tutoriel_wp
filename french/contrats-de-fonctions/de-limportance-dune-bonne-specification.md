# Bien traduire ce qui est attendu

C'est certainement notre tâche la plus difficile. En soi, la programmation est
déjà un effort consistant à écrire des algorithmes qui répondent à notre 
besoin. La spécification nous demande également de faire ce travail, la 
différence est que nous ne nous occupons plus de préciser la manière de répondre
au besoin mais le besoin lui-même. Pour prouver que la réalisation implémente 
bien ce que nous attendons, il faut donc être capable de décrire précisément le
besoin.

Changeons d'exemple et spécifions la fonction suivante :

```c
int max(int a, int b){
  return (a > b) ? a : b;
}
```

Le lecteur pourra écrire et prouver sa spécification. Pour la suite, nous 
travaillerons avec celle-ci :

```c
/*@
  ensures \result >= a && \result >= b;
*/
int max(int a, int b){
  return (a > b) ? a : b;
}
```

Si nous donnons ce code à WP, il accepte sans problème de prouver la fonction. 
Pour autant cette spécification est-elle juste ? Nous pouvons par exemple 
essayer de voir si ce code est validé :

```c
void foo(){
  int a = 42;
  int b = 37;
  int c = max(a,b);

  //@assert c == 42;
}
```

La réponse est non. En fait, nous pouvons aller plus loin en modifiant le corps 
de la fonction ```max``` et remarquer que le code suivant est également valide 
quant à la spécification :

```c
#include <limits.h>

/*@
  ensures \result >= a && \result >= b;
*/
int max(int a, int b){
  return INT_MAX;
}
```

Notre spécification est trop permissive. Il faut que nous soyons plus précis.
Nous attendons du résultat non seulement qu'il soit supérieur ou égal à nos 
deux paramètres mais également qu'il soit exactement l'un des deux :

```c
/*@
  ensures \result >= a && \result >= b;
  ensures \result == a || \result == b;
*/
int max(int a, int b){
  return (a > b) ? a : b;
}
```

# Pointeurs

S'il y a une notion à laquelle nous sommes confrontés en permanence en 
langage C, c'est bien la notion de pointeur. C'est une notion complexe et 
l'une des principales cause de bugs critiques dans les programmes, ils ont 
donc droit à un traitement de faveur dans ACSL.

Prenons par exemple une fonction `swap` pour les entiers :

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

## Historique des valeurs

Ici, nous introduisons une première fonction logique fournie de base par 
ACSL : ```\old```, qui permet de parler de l'ancienne valeur d'un élément. 
Ce que nous dit donc la spécification c'est « la fonction doit assurer que a 
soit égal à l'ancienne valeur (au sens : la valeur avant l'appel) de b et 
inversement ».

La fonction ```\old``` ne peut être utilisée que dans la post-condition d'une
fonction. Si nous avons besoin de ce type d'information ailleurs, nous 
utilisons ```\at``` qui nous permet d'exprimer des propriétés à propos de la 
valeur d'une variable à un point donné. Elle reçoit deux paramètres. Le premier 
est la variable (ou position mémoire) dont nous voulons obtenir la valeur et le 
second la position (sous la forme d'un label C) à laquelle nous voulons 
contrôler la valeur en question.

Par exemple, nous pourrions écrire :

```c
  int a = 42;
 Label_a:
  a = 45;

  //@assert a == 45 && \at(a, Label_a) == 42;
```

En plus des labels que nous pouvons nous-mêmes créer. Il existe 6 labels 
qu'ACSL nous propose par défaut, mais tous ne sont pas supportés par WP :

- ```Pre```/```Old``` : valeur avant l'appel de la fonction,
- ```Post``` : valeur après l'appel de la fonction,
- ```LoopEntry``` : valeur en début de boucle (pas encore supporté),
- ```LoopCurrent``` : valeur en début du pas actuel de la boucle (pas encore
  supporté),
- ```Here``` : valeur au point d'appel.

[[information]]
| Le comportement de ```Here``` est en fait le comportement par défaut lorsque
| nous parlons de la valeur d'une variable. Son utilisation avec ```\at``` nous 
| servira généralement à s'assurer de l'absence d’ambiguïté lorsque nous parlons
| de divers points de programme dans la même expression.

À la différence de ```\old```, qui ne peut être utilisée que dans les 
post-conditions de contrats de fonction, ```\at``` peut être utilisée partout.
En revanche, tous les points de programme ne sont pas accessibles selon le type
d'annotation que nous sommes en train d'écrire. ```Old``` et ```Post``` ne sont 
disponibles que dans les post-conditions d'un contrat, ```Pre``` et ```Here```
sont disponibles partout. ```LoopEntry``` et ```LoopCurrent``` ne sont 
disponibles que dans le contexte de boucles (dont nous parlerons plus loin dans
le tutoriel).

Pour le moment, nous n'utiliserons pas ```\at```, mais elle peut rapidement se
montrer indispensable pour écrire des spécifications précises.

## Validité de pointeurs

Si nous essayons de prouver le fonctionnement de `swap` (en activant
la vérification des RTE), notre post-condition est bien vérifiée mais WP nous 
indique qu'il y a un certain nombre de possibilités de *runtime-error*. Ce qui 
est normal, car nous n'avons pas précisé à WP que les pointeurs que nous
recevons en entrée de fonction sont valides.

Pour ajouter cette précision, nous allons utiliser le prédicat ```\valid``` qui
reçoit un pointeur en entrée :

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

À partir de là, les déréférencements qui sont effectués par la suite sont 
acceptés car la fonction demande à ce que les pointeurs d'entrée soient 
valides.

Comme nous le verrons plus tard, ```\valid``` peut recevoir plus qu'un 
pointeur en entrée. Par exemple, il est possible de lui transmettre une 
expression de cette forme : ```\valid(p + (s .. e))``` qui voudra dire « pour
tout `i` entre `s` et `e` (inclus), `p+i` est un pointeur valide », ce sera important 
notamment pour la gestion des tableaux dans les spécifications.

Si nous nous intéressons aux assertions ajoutées par WP dans la fonction `swap`
avec la validation des RTEs, nous pouvons constater qu'il existe une variante
de ```\valid``` sous le nom ```\valid_read```. Contrairement au premier, 
celui-ci assure que le pointeur peut être déréférencé mais en lecture 
seulement. Cette subtilité est due au fait qu'en C, le *downcast* de pointeur 
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
de modifier. Par exemple pour la fonction `swap` :

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
assertions que nous avions demandées dans le `main` seront validées par WP.

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
Le lecteur pourra maintenant reprendre les exemples précédents pour y intégrer 
la bonne clause ```assigns``` ;) .

## Séparation des zones de la mémoire

Les pointeurs apportent le risque d'*aliasing* (plusieurs pointeurs ayant accès à
la même zone de mémoire). Si dans certaines fonctions, cela ne pose pas de 
problème (par exemple si nous passons deux pointeurs égaux
à notre fonction ```swap```, la spécification est toujours vérifiée par le 
code source), dans d'autre cas, ce n'est pas si simple :

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
   ```*a == \old(*a) + *a```, ce qui ne peut être vrai que si l'ancienne valeur 
   pointée par ```a``` était 0, ce qu'on ne sait pas,
- la propriété ```*b == \old(*b)``` n'est pas validée car potentiellement,
  nous la modifions.

[[question]]
| Pourquoi la clause `assign` est-elle validée ?
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