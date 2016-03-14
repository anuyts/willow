module willow.cat.DaggerCategories where

open import willow.cat.Categories public
open import willow.cat.DaggerCategory public

cDCat : (ℓo ℓh : Level) → Cat (lsuc (ℓo ⊔ ℓh)) (ℓo ⊔ ℓh)
Cat.Obj (cDCat ℓo ℓh) = DCat ℓo ℓh
Cat.Hom (cDCat ℓo ℓh) dcA dcB = dcA dc→ dcB
Cat.id (cDCat ℓo ℓh) dcA = dc-id dcA
Cat.comp (cDCat ℓo ℓh) dcg dcf = dcg dc∘ dcf
Cat.m∘assoc (cDCat ℓo ℓh) = dfunctorext (functorext refl)
Cat.m∘lunit (cDCat ℓo ℓh) = dfunctorext (functorext refl)
Cat.m∘runit (cDCat ℓo ℓh) = dfunctorext (functorext refl)

cforgetDagger : {ℓo ℓh : Level} → cDCat ℓo ℓh ++> cCat ℓo ℓh
_++>_.obj cforgetDagger = dc.cat
_++>_.hom cforgetDagger = df.f
_++>_.hom-id cforgetDagger dcA = refl
_++>_.hom-m∘ cforgetDagger ψ φ = refl
