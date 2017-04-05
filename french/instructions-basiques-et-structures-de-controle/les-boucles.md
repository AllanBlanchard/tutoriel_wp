Les boucles ont besoin d'un traitement de faveur dans la vérification déductive
de programmes. Ce sont les seules structures de contrôle qui vont nécessiter un
travail conséquent de notre part. Nous ne pouvons pas y échapper car sans les 
boucles nous pouvons difficilement prouver des programmes intéressants. 

Avant de s'intéresser à la spécification des boucles, il est légitime de se 
poser la question suivante : pourquoi les boucles sont-elles compliquées ?

# Induction et invariance

La nature des boucles rend leur analyse difficile. Lorsque nous faisons nos 
raisonnements arrières, il nous faut une règle capable de dire à partir de la
post-condition quelle est la pré-condition d'une certaine séquence 
d'instructions. Problème : nous ne pouvons *a priori* pas déduire combien de 
fois la boucle va s'exécuter et donc par conséquent, nous ne pouvons pas non 
plus savoir combien de fois les variables ont été modifiées.

Nous allons donc procéder en raisonnant par induction. Nous devons trouver une
propriété qui est vraie avant de commencer la boucle et qui si elle est vraie
en début d'un tour de boucle, sera vraie à la fin (et donc par extension, au 
début du tour suivant).

Ce type de propriété est appelé un invariant de boucle. Un invariant de boucle
est une propriété qui doit est vraie avant et après chaque tour d'une boucle. 
Par exemple, pour la boucle :

```c
for(int i = 0 ; i < 10 ; ++i){ /* */ }
```

La propriété $0 <= i <= 10$ est un invariant de la boucle. La propriété 
$-42 <= i <= 42$ est également un invariant de la boucle (qui est nettement
plus imprécis néanmoins). La propriété $0 < i <= 10$ n'est pas un invariant,
elle n'est pas vraie à l'entrée de la boucle. La propriété $0 <= i < 10$ 
**n'est pas un invariant de la boucle**, elle n'est pas vraie à la fin du 
dernier tour de la boucle qui met la valeur $i$ à $10$.

Le raisonnement produit par l'outil pour vérifier un invariant $I$ sera donc :

- vérifions que $I$ est vrai au début de la boucle (établissement),
- vérifions que $I$ est vrai avant de commencer un tour, alors $I$ vrai après (préservation).

## [Formel] Règle d'inférence

En notant l'invariant $I$, la règle d'inférence correspondant à la boucle est 
définie comme suit :

-> $\dfrac{\{I \wedge B \}\ c\ \{I\}}{\{I\}\ while(B)\{c\}\ \{I \wedge \neg B\}}$ <-

Et le calcul de plus faible pré-condition est le suivant :

-> $wp(while (B) \{ S \}, Post) = I \wedge ((B \wedge I) \Rightarrow wp(S, I)) \wedge ((\neg B \wedge I) \Rightarrow Post)$ <-

Détaillons cette formule :

- (1) le premier $I$ correspond à l'établissement de l'invariant, c'est 
  vulgairement la "pré-condition" de la boucle,
- la deuxième partie de la conjonction ($(B \wedge I) \Rightarrow wp(S, I)$)
  correspond à la vérification du travail effectué par le corps de la boucle :
    - la pré-condition que nous connaissons du corps de la boucle (notons $KWP$, 
      "Known WP") , c'est ($KWP = B \wedge I$). Soit le fait que nous sommes
      rentrés dedans ($B$ est vrai), et que l'invariant est respecté à ce moment
      ($I$, qui est vrai avant de commencer la boucle par 1, et dont veut 
      vérifier qu'il sera vraie en fin de bloc de la boucle (2)), 
    - (2) ce qu'il nous reste à vérifier c'est que $KWP$ implique la 
	  pré-condition réelle\* du bloc de code de la boucle 
          ($KWP \Rightarrow wp(S, Post)$). Ce que nous voulons en fin de bloc, 
          c'est avoir maintenu l'invariant $I$ ($B$ n'est peut-être plus vrai en
          revanche). Donc 
	  $KWP \Rightarrow wp(S, I)$, soit $(B \wedge I) \Rightarrow wp(S, I)$,
    - \* cela correspond à une application de la règle de conséquence expliquée
      précédemment.
- finalement la dernière partie ($(\neg B \wedge I) \Rightarrow Post$)
  nous dit que le fait d'être sorti de la boucle ($\neg B$), tout en ayant 
  maintenu l'invariant $I$, doit impliquer la post-condition voulue pour la 
  boucle.

## Retour à l'outil

Il existe des outils capables d'inférer des invariants (pour peu qu'ils soient
simples, les outils automatiques restent limités). Ce n'est pas le cas de WP. 
Il nous faut donc écrire nos invariants à la main. Pour cela nous ajoutons les 
annotations suivantes en début de boucle :

```c
int main(){
  int i = 0;
  
  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
}
```

[[attention]]
| **RAPPEL** : L'invariant est bien : i **<=** 30 !

Pourquoi ? Parce que tout au long de la boucle ```i``` sera bien compris entre
0 et 30 **inclus**. 30 est même la valeur qui nous permettra de sortir de la 
boucle. Plus encore, une des propriétés demandées par le calcul de plus faible
pré-conditions sur les boucles est que lorsque l'on invalide la condition de la
boucle, par la connaissance de l'invariant, on peut prouver la post-condition 
(Formellement : $(\neg B \wedge I) \Rightarrow Post$).

La post-condition de notre boucle est ```i == 30```. Et doit être impliquée par
$\neg$ ```i < 30``` $\wedge$ ```0 <= i <= 30```. Ici, cela fonctionne 
bien : ```i >= 30 && 0 <= i <= 30 ==> i == 30```. Si l'invariant excluait 
l'égalité à 30, la post-condition ne serait pas atteignable.

Une nouvelle fois, nous pouvons jeter un œil à la liste des buts dans WP 
Goals :

![Obligations générées pour prouver notre boucle](https://zestedesavoir.com:443/media/galleries/2584/3e2cfa83-cbf8-48fd-b716-9baf51a91ed3.png)

Nous remarquons bien que WP décompose la preuve de l'invariant en deux parties : 
l'établissement de l'invariant et sa préservation. WP produit exactement le 
raisonnement décrit plus haut pour la preuve de l'assertion. Dans les versions
récentes de Frama-C, Qed est devenu particulièrement puissant, et l'obligation de
preuve générée ne le montre pas (affichant simplement "True"). En utilisant 
l'option ```-wp-no-simpl``` au lancement, nous pouvons quand même voir 
l'obligation correspondante :

![Preuve de l'assertion par connaissance de l'invariant et l'invalidation de la condition de boucle](https://zestedesavoir.com:443/media/galleries/2584/e74c959b-b551-437e-827f-7a01732101b5.png)

Mais notre spécification est-elle suffisante ?

```c
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
```
Voyons le résultat :

![Encore des effets de bord](https://zestedesavoir.com:443/media/galleries/2584/6243b4fe-2c54-4762-babf-ba1229c4b665.png)

Il semble que non. 

# La clause "assigns" ... pour les boucles

En fait, à propos des boucles, WP ne considère vraiment *que* ce que lui 
fournit l'utilisateur pour faire ses déductions. Et ici l'invariant ne nous dit
rien à propos de l'évolution de la valeur de ```h```. Nous pourrions signaler 
l'invariance de toute variable du programme mais ce serait beaucoup d'efforts. 
ACSL nous propose plus simplement d'ajouter des annotations ```assigns``` pour 
les boucles. Toute autre variable est considérée invariante. Par exemple :

```c
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
```

Cette fois, nous pouvons établir la correction de la boucle. Par contre rien ne
nous prouve sa terminaison. L'invariant de boucle n'est pas suffisant pour 
effectuer une telle preuve. Par exemple, dans notre programme, si nous réécrivons 
la boucle comme ceci :

```c
/*@
  loop invariant 0 <= i <= 30;
  loop assigns i;
*/
while(i < 30){
   
}
```

L'invariant est bien vérifié également, mais nous ne pourrons jamais prouver
que la boucle termine : elle est infinie.

# Preuve partielle et preuve totale - Variant de boucle

En vérification déductive, il y a deux types de correction, la correction 
partielle et la correction totale. Dans le premier cas, la formulation est 
"si la pré-condition est validée et **si** le calcul termine, alors la 
post-condition est validée". Dans le second cas, "si la pré-condition est 
validée, alors le calcul termine et la post-condition est validée". WP 
s'intéresse par défaut à de la preuve partielle :

```c
void foo(){
  while(1){}
  //assert \false;
}
```
Si nous demandons la vérification de ce code en activant le contrôle de RTE,
nous obtenons ceci :

![Preuve de faux par non-terminaison de boucle](https://zestedesavoir.com:443/media/galleries/2584/dba607cc-eb6e-4f8a-83b5-89f353981615.png)

L'assertion "FAUX" est prouvée ! La raison est simple : la non-terminaison de
la boucle est triviale. Comme le calcul ne termine pas et nous sommes en 
correction partielle, nous prouve ce que nous voulons à la suite d'un calcul 
non terminant. Si la non-terminaison est non-triviale, il y a peu de chances 
que l'assertion soit prouvée en revanche.


[[information]]
| À noter qu'une assertion inatteignable est toujours prouvée vraie de cette 
| manière :
| ![Assertion que l'on saute par un Goto](https://zestedesavoir.com:443/media/galleries/2584/eafe5462-e97f-4b9b-8581-c8d9b4ecca5c.png)
| 
| Et c'est également le cas lorsque l'on sait trivialement qu'une instruction
| produit nécessairement une erreur d'exécution (par exemple en déréférençant 
| la valeur ```NULL```), comme nous avions déjà pu le constater avec l'exemple
| de l'appel à ```abs``` avec la valeur ```INT_MIN```.

Pour prouver la terminaison d'une boucle, nous utilisons la notion de variant de 
boucle. Le variant de boucle n'est pas une propriété mais une valeur. C'est une 
expression faisant intervenir des éléments modifiés par la boucle et donnant une
borne supérieure sur le nombre d'itérations restant à effectuer à un tour de la
boucle. C'est donc une expression supérieure à 0 et strictement décroissante d'un 
tour de boucle à l'autre (cela sera également vérifié par induction par WP).

Si nous reprenons notre programme précédent, nous pouvons ajouter le variant
de cette façon :

```c
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}
```

Une nouvelle fois nous pouvons regarder les buts générés :

![Notre simple boucle complètement spécifiée et prouvée](https://zestedesavoir.com:443/media/galleries/2584/077e05ac-1841-4a19-9309-000807fc35bf.png)

Le variant nous génère bien deux obligations au niveau de la vérification : 
assurer que la valeur est positive, et assurer qu'elle décroît strictement pendant
l'exécution de la boucle. Et si nous supprimons la ligne de code qui incrémente
`i`, WP ne peut plus prouver que la valeur `30 - i` décroît strictement.

# Lier la post-condition et l'invariant

Supposons le programme spécifié suivant. Notre but est de prouver que le retour
de cette fonction est l'ancienne valeur de `a` à laquelle nous avons ajouté 10.

```c
/*@
    ensures \result == \old(a) + 10;
*/
int plus_dix(int a){
    /*@
        loop invariant 0 <= i <= 10;
        loop assigns i, a;
        loop variant 10 - i;
    */
    for (int i = 0; i < 10; ++i)
        ++a;

    return a;
}
```

Le calcul de plus faibles pré-conditions ne permet pas de sortir de la boucle des
informations qui ne font pas partie de l'invariant. Dans un programme comme :

```c
/*@
    ensures \result == \old(a) + 10;
*/
int plus_dix(int a){
    ++a;
    ++a;
    ++a;
    //...
    return a;
}
```

En remontant les instructions depuis la post-condition, on conserve toujours les 
informations à propos de `a`. À l'inverse, comme mentionné plus tôt, en dehors de
la boucle WP ne considérera que les connaissances fournies par notre invariant. 
Par conséquent, notre fonction `plus_dix` ne peut pas être prouvée en l'état : 
l'invariant ne mentionne aucune connaissance à propos de `a`. Pour lier notre
post-condition à l'invariant, il faut ajouter une telle connaissance. Par 
exemple :

```c
/*@
    ensures \result == \old(a) + 10;
*/
int plus_dix(int a){
    /*@
        loop invariant 0 <= i <= 10;
        loop invariant a = \old(a) + i; //< AJOUT
        loop assigns i, a;
        loop variant 10 - i;
    */
    for (int i = 0; i < 10; ++i)
        ++a;

    return a;
}
```

[[information]]
| Ce besoin peut semble être une contrainte très forte. Elle ne l'est en fait pas
| tant que cela. Il existe des analyses fortement automatiques capables de 
| calculer les invariants de boucles. Par exemple, sans spécifications, une 
| interprétation abstraite calculera assez facilement `0 <= i <= 10` et 
| `\old(a) <= a <= \old(a)+10`. En revanche, il est souvent bien plus difficile
| de calculer les relations qui existent entre des variables différentes qui 
| évoluent dans le même programme, par exemple l'égalité mentionnée par notre 
| invariant ajouté.
| 
