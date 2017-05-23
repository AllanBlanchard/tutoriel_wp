Dans cette partie, nous avons vu les constructions de ACSL qui nous permettent 
de factoriser un peu nos spécifications et d'exprimer des propriétés générales 
pouvant être utilisées par les prouveurs pour faciliter leur travail.

Toutes les techniques expliquées dans cette partie sont sûres, au sens où 
elles ne permettent *a priori* pas de fausser la preuve avec des définitions 
fausses ou contradictoires. En tous cas, si la spécification n'utilise que ce
type de constructions et que chaque lemme, chaque pré-condition (aux points 
d'appels), chaque post-condition, chaque assertion, chaque variant et chaque 
invariant est correctement prouvé, le code est juste.

Parfois ces constructions ne sont pas suffisantes pour exprimer toutes nos 
propriétés ou pour prouver nos programmes. Les prochaines constructions que nous
allons voir vont nous ajouter de nouvelles possibilités à ce sujet, mais il 
faudra se montrer prudent dans leur usage car des erreurs pourraient nous 
permettre de créer des hypothèses fausses ou d'altérer le programme que nous 
vérifions.