
# Règle de conséquence

Parfois, il peut être utile pour la preuve d'affaiblir une post-condition ou de
renforcer une pré-condition. Si la première sera souvent établie par nos soins
 pour faciliter le travail du prouveur, la seconde est plus souvent vérifiée 
 par l'outil à l'issu du calcul de plus faible pré-condition.

La règle d'inférence en logique de Hoare est la suivante :

->$\dfrac{P \Rightarrow SP \quad \{SP\}\quad c\quad \{WQ\} \quad WQ \Rightarrow Q}{\{P\}\quad c \quad \{Q\}}$<-

(Nous noterons que les prémisses, ici, ne sont pas seulement des triplets de
Hoare mais également des formules à vérifier)

Par exemple, si notre post-condition est trop complexe, elle risque de générer
une plus faible pré-condition trop compliquée et de rendre le calcul des 
prouveurs difficile. Nous pouvons alors créer une post-condition intermédiaire
$WQ$, plus simple, mais plus restreinte et impliquant la vraie post-condition. 
C'est la partie $WQ \Rightarrow Q$.

Inversement, le calcul de pré-condition générera généralement une formule 
compliquée et souvent plus faible que la pré-condition que nous souhaitons
accepter en entrée. Dans ce cas, c'est notre outil qui s'occupera de vérifier 
l'implication entre ce que nous voulons et ce qui est nécessaire pour que notre
code soit valide. C'est la partie $P \Rightarrow SP$.

# Règle de constance

Certaines séquences d'instructions peuvent concerner et faire intervenir des 
variables différentes. Ainsi, il peut arriver que nous initialisions et manipulions
un certain nombre de variables, que nous commencions à utiliser certaines d'entre 
elles, puis que nous les délaissions au profit d'autres pendant un temps. Quand un
tel cas apparaît, nous avons envie que l'outil ne se préoccupe que des variables 
qui sont susceptibles d'être modifiées pour avoir des propriétés les plus légères 
possibles.

La règle d'inférence qui définit ce raisonnement est la suivante :

-> $\dfrac{\{P\}\quad c\quad \{Q\}}{\{P \wedge R\}\quad c\quad \{Q \wedge R\}}$ <-

Où $c$ ne modifie aucune variable entrant en jeu dans $R$. Ce qui nous dit : "pour vérifier le triplet, débarrassons nous des parties de la formule qui concerne des
variables qui ne sont pas manipulées par $c$ et prouvons le nouveau triplet". 
