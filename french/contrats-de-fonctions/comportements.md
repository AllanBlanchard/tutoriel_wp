Il peut arriver qu'une fonction ait divers comportements potentiellement très
différents en fonction de l'entrée. Un cas typique est la réception d'un 
pointeur vers une ressource optionnelle : si le pointeur est ```NULL```, nous 
aurons un certain comportement et un comportement complètement différent s'il ne 
l'est pas.

Nous avons déjà vu une fonction qui avait des comportements différents, la 
fonction ```abs```. Nous allons la reprendre comme exemple. Les deux 
comportements que nous pouvons isoler sont le cas où la valeur est positive et
le cas où la valeur est négative.

Les comportements nous servent à spécifier les différents cas pour les 
post-conditions. Nous les introduisons avec le mot-clé ```behavior```. 
Chaque comportement se voit attribuer un nom, les suppositions du cas que 
nous traitons introduites par le mot clé ```assumes``` et la 
post-condition associée. Finalement, nous pouvons également demander à WP
de vérifier le fait que les comportements sont disjoints (pour garantir 
le déterminisme) et complets.

Les comportements sont disjoints si pour toute entrée de la fonction, elle ne
correspond aux suppositions (assumes) que d'un seul comportement. Les 
comportements sont complets si les suppositions recouvrent bien tout le domaine
des entrées.

Par exemple pour ```abs``` :

```c
/*@
  requires val > INT_MIN;
  assigns  \nothing;

  behavior pos:
    assumes 0 <= val;
    ensures \result == val;
  
  behavior neg:
    assumes val < 0;
    ensures \result == -val;
 
  complete behaviors;
  disjoint behaviors;
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

Pour comprendre ce que font précisément ```complete``` et ```disjoint```, il est utile
d'expérimenter deux possibilités : 

- remplacer la supposition de "pos" par ```val > 0``` auquel cas les 
  comportements seront disjoints mais incomplets (il nous manquera le cas 
  ```val == 0```)
- remplacer la supposition de "neg" par ```val <= 0``` auquel cas les 
  comportements seront complets mais non disjoints (le cas ```val == 0```) sera
  présent dans les deux comportements.

[[attention]]
| Même si ```assigns``` est une post-condition, à ma connaissance, il n'est pas 
| possible de mettre des ```assigns``` pour chaque behavior. Si nous avons
| besoin d'un tel cas, nous spécifions :
|
| - ```assigns``` avant les behavior (comme dans notre exemple) avec tout 
|   élément non-local susceptible d'être modifié, 
| - en post-condition de chaque behavior les éléments qui ne sont finalement 
|   pas modifiés en les indiquant égaux à leur ancienne (```\old```) valeur.

Les comportements sont très utiles pour simplifier l'écriture de spécifications
quand les fonctions ont des effets très différents en fonction de leurs 
entrées. Sans eux, les spécifications passent systématiquement par des 
implications traduisant la même idée mais dont l'écriture et la lecture sont 
plus difficiles (nous sommes susceptibles d'introduire des erreurs). 

D'autre part, la traduction de la complétude et de la disjonction devraient 
être écrites manuellement, ce qui serait fastidieux et une nouvelle fois source
d'erreurs.
