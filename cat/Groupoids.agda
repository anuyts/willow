module aken.cat.Groupoids where

open import aken.cat.Groupoid public
open import aken.cat.Categories public

cGrpd : (ℓo ℓh : Level) → Cat (lsuc (ℓo ⊔ ℓh)) (ℓo ⊔ ℓh)
cGrpd ℓo ℓh = record
  { Obj = Groupoid ℓo ℓh
  ; Hom = λ gA gB → g.cat gA ++> g.cat gB
  ; id = λ gA → c-id (g.cat gA)
  ; comp = _c∘_
  ; m∘assoc = λ {gA gB gC gD ch cg cf} → functorext (pair-ext refl refl)
  ; m∘lunit = λ {gA gB cf} → functorext (pair-ext refl refl)
  ; m∘runit = λ {gA gB cf} → functorext (pair-ext refl refl)
  }

cforgetGrpd : {ℓo ℓh : Level} → cGrpd ℓo ℓh ++> cCat ℓo ℓh
cforgetGrpd = record
  { obj = g.cat
  ; hom = λ {gA gB} → idf
  ; hom-id = λ gA → refl
  ; hom-m∘ = λ cg cf → refl
  }
