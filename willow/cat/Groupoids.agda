module willow.cat.Groupoids where

open import willow.cat.Groupoid public
open import willow.cat.Categories public

cGrpd : (ℓo ℓh : Level) → Cat (lsuc (ℓo ⊔ ℓh)) (ℓo ⊔ ℓh)
Cat.Obj (cGrpd ℓo ℓh) = Groupoid ℓo ℓh
Cat.Hom (cGrpd ℓo ℓh) gA gB = g.cat gA ++> g.cat gB
Cat.id (cGrpd ℓo ℓh) gA = c-id (g.cat gA)
Cat.comp (cGrpd ℓo ℓh) = _c∘_
Cat.m∘assoc' (cGrpd ℓo ℓh) {gA} {gB} {gC} {gD} {ch} {cg} {cf} = functorext (pair-ext refl refl)
Cat.m∘lunit' (cGrpd ℓo ℓh) {gA} {gB} {cf} = functorext (pair-ext refl refl)
Cat.m∘runit' (cGrpd ℓo ℓh) {gA} {gB} {cf} = functorext (pair-ext refl refl)

cforgetGrpd : {ℓo ℓh : Level} → cGrpd ℓo ℓh ++> cCat ℓo ℓh
f.obj cforgetGrpd = g.cat
f.hom cforgetGrpd {gA} {gB} = idf
f.hom-id' cforgetGrpd gA = refl
f.hom-m∘' cforgetGrpd cg cf = refl
