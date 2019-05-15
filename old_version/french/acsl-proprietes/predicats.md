Un prédicat est une propriété portant sur des objets et pouvant être vraie ou 
fausse. En résumé, des prédicats, c'est ce que nous écrivons depuis le début de
ce tutoriel dans les clauses de nos contrats et de nos invariants de boucle. 
ACSL nous permet de créer des versions nommées de ces prédicats, à la manière 
d'une fonction booléenne en C par exemple. À la différence près tout de même que
les prédicats (ainsi que les fonctions logiques que nous verrons par la suite) 
doivent être pures, c'est-à-dire qu'elles ne peuvent pas produire d'effets de 
bords en modifiant des valeurs pointées par exemple.

Ces prédicats peuvent prendre un certain nombre de paramètres. En plus de cela,
ils peuvent également recevoir un certain nombre de *labels* (au sens C du terme) 
qui vont permettre d'établir des relations entre divers points du code. 

# Syntaxe

Les prédicats sont, comme les spécifications, introduits au travers 
d'annotations. La syntaxe est la suivante :

```c
/*@
  predicate nom_du_predicat { Label0, Label1, ..., LabelN }(type0 arg0, type1 arg1, ..., typeN argN) =
    //une relation logique entre toutes ces choses.
*/
```

Nous pouvons par exemple définir le prédicat nous disant qu'un entier en mémoire n'a
pas changé entre deux points particuliers du programme :

```c
/*@
  predicate unchanged{L0, L1}(int* i) =
    \at(*i, L0) == \at(*i, L1);
*/
```

[[attention]]
| Gardez bien en mémoire que le passage se fait, comme en C, par valeur. Nous ne
| pouvons pas écrire ce prédicat en passant directement `i` :
| ```c
| /*@
|   predicate unchanged{L0, L1}(int i) =
|     \at(i, L0) == \at(i, L1);
|  */
| ```
| Car `i` est juste une copie de la variable reçue en paramètre.

Nous pouvons par exemple vérifier ce petit code :

```c
int main(){
  int i = 13;
  int j = 37;

 Begin:
  i = 23;
 
  //@assert ! unchanged{Begin, Here}(&i);
  //@assert   unchanged{Begin, Here}(&j);
}
```

Nous pouvons également regarder les buts générés par WP et constater que, 
même s'il subit une petite transformation syntaxique, le prédicat n'est pas 
déroulé par WP. Ce sera au prouveur de déterminer s'il veut raisonner avec.

Comme nous l'avons dit plus tôt, une des utilités des prédicats et fonctions (que 
nous verrons un peu plus tard) est de rendre plus lisible nos spécifications et 
de les factoriser. Un exemple est d'écrire un prédicat pour la validité en 
lecture/écriture d'un tableau sur une plage particulière. Cela nous évite d'avoir
à réécrire l'expression en question qui est moins compréhensible au premier 
coup d’œil.

```c
/*@
  predicate valid_range_rw(int* t, integer n) =
    n >= 0 && \valid(t + (0 .. n-1));

  predicate valid_range_ro(int* t, integer n) =
    n >= 0 && \valid_read(t + (0 .. n-1));
*/

/*@
  requires 0 < length;
  requires valid_range_ro(array, length);
  //...
*/
int* search(int* array, size_t length, int element)
```

Dans cette portion de spécification, le *label* pour les prédicats n'est pas 
précisé, ni pour leur création, ni pour leur utilisation. Pour la création, 
Frama-C va automatiquement en ajouter un dans la définition du prédicat. 
Pour l'appel, le *label* passé sera implicitement ```Here```. La non-déclaration
du *label* dans la définition n'interdit pour autant pas de passer explicitement
un *label* lors de l'appel.

Bien entendu, les prédicats peuvent être déclarés dans des fichiers *headers* afin
de produire une bibliothèque d'utilitaires de spécifications par exemple.

# Abstraction

Une autre utilité importante des prédicats est de définir l'état logique de nos
structures quand les programmes se complexifient. Nos structures doivent 
généralement respecter un invariant (encore) que chaque fonction de manipulation
devra maintenir pour assurer que la structure sera toujours utilisable et 
qu'aucune fonction ne commettra de bavure.

Cela permet notamment de faciliter la lecture de spécifications. Par exemple, nous
pourrions poser les spécifications nécessaires à la sûreté d'une pile de taille 
limitée. Et cela donnerait quelque chose comme :

```c
struct stack_int{
  size_t top;
  int    data[MAX_SIZE];
};

/*@
  predicate valid_stack_int(struct stack_int* s) = // à définir ;
  predicate empty_stack_int(struct stack_int* s) = // à définir ;
  predicate full_stack_int(struct stack_int* s) =  // à définir ;
*/

/*@
  requires \valid(s);
  assigns *s;
  ensures valid_stack_int(s) && empty_stack_int(s);
*/
void initialize(struct stack_int* s);

/*@
  requires valid_stack_int(s) && !full_stack_int(s);
  assigns  *s;
  ensures valid_stack_int(s);
*/
void push(struct stack_int* s, int value);

/*@
  requires valid_stack_int(s) && !empty_stack_int(s);
  assigns \nothing;
*/
int  top(struct stack_int* s);

/*@
  requires valid_stack_int(s) && !empty_stack_int(s);
  assigns *s;
  ensures valid_stack_int(s);
*/
void pop(struct stack_int* s);

/*@
  requires valid_stack_int(s);
  assigns \nothing;
  ensures \result == 1 <==> empty_stack_int(s);
*/
int  is_empty(stack_int_t s);


/*@
  requires valid_stack_int(s);
  assigns \nothing;
  ensures \result == 1 <==> full_stack_int(s);
*/
int  is_full(stack_int_t s);
```

Ici la spécification n'exprime pas de propriétés fonctionnelles. Par exemple, 
rien ne nous spécifie que lorsque nous faisons un *push* d'une valeur puis que nous
demandons *top*, nous auront effectivement cette valeur. Mais elle nous donne 
déjà tout ce dont nous avons besoin pour produire un code où, à défaut d'avoir 
exactement les résultats que nous attendons (des comportements tels que « si 
j'empile une valeur $v$, l'appel à `top` renvoie la valeur $v$ », par exemple), nous
 pouvons au moins garantir que nous n'avons pas d'erreur d'exécution (à condition 
de poser une spécification correcte pour nos prédicats et de prouver les fonctions 
d'utilisation de la structure).
