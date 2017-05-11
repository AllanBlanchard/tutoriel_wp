Dans cette partie, nous avons vu les constructions de ACSL qui nous permettent 
de factoriser un peu nos spécifications et d'exprimer des propriétés générales 
pouvant être utilisées par les prouveurs pour faciliter leur travail.

Toutes les techniques expliquées dans cette partie sont sûres, au sens où 
elles ne permettent *a priori* pas de fausser la preuve avec des définitions 
fausses ou contradictoire. En tout cas, si elles ont toutes été prouvées 
correctes : tous les lemmes, toutes les pré-conditions aux points d'appels, 
toutes les assertions, tous les invariants et variants, ainsi que toutes les 
post-conditions.

Parfois ces constructions ne sont pas suffisantes pour exprimer toutes nos 
propriétés ou pour prouver nos programmes. Les prochaines constructions que nous
allons voir vont nous ajouter de nouvelles possibilités à ce sujet, mais il 
faudra se montrer prudent dans leur usage car des erreurs pourraient nous 
permettre de créer des hypothèses fausses ou d'altérer le programme que nous 
vérifions.