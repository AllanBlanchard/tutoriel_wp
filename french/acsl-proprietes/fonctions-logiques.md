Les fonctions logiques nous permettent de décrire des fonctions qui ne seront 
utilisables que dans les spécifications. Cela nous permet, d'une part, de les 
factoriser, et d'autre part de définir des opérations sur les types integer et 
real qui ne peuvent pas déborder contrairement aux types machines.

Comme les prédicats, elles peuvent recevoir divers labels et valeurs en 
paramètre.

# Syntaxe

Pour déclarer une fonction logique, l'écriture est la suivante :

```c
/*@
  logic type_retour ma_fonction{ Label0, ..., LabelN }( type0 arg0, ..., typeN argN ) =
    formule mettant en jeu les arguments ;
*/
``` 

Nous pouvons par exemple décrire une fonction affine générale du côté de
la logique :

```c
/*@
  logic integer ax_b(integer a, integer x, integer b) =
    a * x + b;
*/
```

Elle peut nous servir à prouver le code de la fonction suivante :

```c
/*@ 
  assigns \nothing ;
  ensures \result == ax_b(3,x,4); 
*/
int function(int x){
  return 3*x + 4;
}
```

![Les débordements semblent pouvoir survenir](https://zestedesavoir.com:443/media/galleries/2584/e34ccc72-b7ea-46cf-9875-16c3d57262af.png)

Le code est bien prouvé mais les contrôles d'overflow, eux, ne le sont pas. Nous 
pouvons à nouveau définir des fonctions logiques générales pour avoir les bornes 
calculées de côté de la logique en fonction des valeurs que nous donnons en 
entrée. Ainsi qu'ajouter nos contrôles de bornes en pré-condition de fonction :

```c
/*@
  logic integer limit_int_min_ax_b(integer a, integer b) =
    (a == 0) ? (b > 0) ? INT_MIN : INT_MIN-b :
    (a <  0) ? (INT_MAX-b)/a :
               (INT_MIN-b)/a ;

  logic integer limit_int_max_ax_b(integer a, integer b) =
    (a == 0) ? (b > 0) ? INT_MAX-b : INT_MAX :
    (a <  0) ? (INT_MIN-b)/a :
               (INT_MAX-b)/a ;
*/

/*@
  requires limit_int_min_ax_b(3,4) < x < limit_int_max_ax_b(3,4);
  assigns \nothing ;
  ensures \result == ax_b(3,x,4);
*/
int function(int x){
  return 3*x + 4;
}
```

Et cette fois tout est prouvé. Évidemment, nous pourrions fixer ces valeurs en 
dur chaque fois que nous avons besoin d'une nouvelle fonction affine du côté de
la logique mais en posant ces fonctions, nous obtenons directement ces valeurs 
sans avoir besoin de les calculer nous même, ce qui est assez confortable.

# Récursivité et limites

Les fonctions logiques peuvent être définie récursivement. Cependant, une telle
définition va très rapidement montrer ses limites pour la preuve. En effet, 
pendant les manipulations des prouveurs automatiques sur les propriétés 
logiques, si l'usage d'une telle fonction est présente, elle devra être évaluée,
or les prouveurs ne sont pas conçus pour faire ce genre d'évaluation qui se 
révélera donc généralement très coûteuse, produisant alors des temps de preuve
trop longs menant à des *timeouts*. 

Exemple concret, nous pouvons définir la fonction factorielle, dans la logique
et en C :

```c
/*@
  logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);
*/

/*@ 
  assigns \nothing ;
  ensures \result == factorial(n) ; 
*/
unsigned facto(unsigned n){
  return (n == 0) ? 1 : n * facto(n-1);
}
```

Sans contrôle de borne, cette fonction se prouve rapidement. Si nous ajoutons
le contrôle des RTE, le vérification de débordement sur l'entier non-signé n'est
pas ajoutée, car c'est un comportement déterminé d'après la norme C. Pour ajouter
une assertion à ce point, nous pouvons demander à WP de générer ses propres 
vérifications en faisant un clic droit sur la fonction puis "insert WP-safety 
guards". Et dans ce cas, le nom débordemement n'est pas prouvé.

Sur le type unsigned, le maximum que nous pouvons calculer est la factorielle de 
12. Au-delà, cela produit un dépassement. Nous pouvons donc ajouter cette 
pré-condition :

```c
/*@ 
  requires n <= 12 ;
  assigns \nothing ;
  ensures \result == factorial(n) ; 
*/
unsigned facto(unsigned n){
  return (n == 0) ? 1 : n * facto(n-1);
}
```

Si nous demandons la preuve avec cette entrée, Alt-ergo échouera pratiquement à 
coup sûr. En revanche, le prouveur Z3 produit la preuve en moins d'une seconde.
Parce que dans ce cas précis, les heuristiques de Z3 considèrent que c'est une
bonne idée de passer un peu plus de temps sur l'évaluation de la fonction. Nous
pouvons par exemple changer la valeur maximale de "n" pour voir comment se 
comporte les différents prouveurs. Avec un "n" maximal fixé à 9, Alt-ergo produit
la preuve en moins de 10 secondes, tandis que pour une valeur à 10, même une 
minute ne suffit pas.

Les fonctions logiques peuvent donc être définie récursivement mais sans astuces
supplémentaires, nous venons vite nous heurter au fait que les prouveurs vont au 
choix devoir faire de l'évaluation, ou encore "raisonner" par induction, deux 
tâches pour lesquelles ils ne sont pas du tout fait, ce qui limite nos 
possibilités de preuve.
