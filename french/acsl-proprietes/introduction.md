Depuis le début de ce tutoriel, nous avons vu divers prédicats et fonctions 
logiques qui sont fournis par défaut en ACSL : ```\valid```, ```\valid_read```,
```\separated```, ```\old``` et ```\at```. Il en existe bien sûr d'autres mais 
nous n'allons pas les présenter un à un, le lecteur pourra se référer à 
[la documentation (ACSL implementation)](http://frama-c.com/download.html) 
pour cela (à noter : tout n'est pas nécessairement supporté par WP).

ACSL nous permet de faire plus que « simplement » spécifier notre code. Nous 
pouvons définir nos propres prédicats, fonctions, relations, etc. Le but est de
pouvoir abstraire nos spécifications. Cela nous permet de les factoriser (par 
exemple en définissant ce qu'est un tableau valide), ce qui a deux effets 
positifs pour nous : d'abord nos spécifications deviennent plus lisibles donc 
plus faciles à comprendre, mais cela permet également de réutiliser des preuves
déjà faites et donc de faciliter la preuve de nouveaux programmes.