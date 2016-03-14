module willow.cat.DaggerCategories.BidirFunctor where

open import willow.cat.DaggerCategories public

cbidir : ∀{ℓo ℓh} → cCat ℓo ℓh ++> cDCat ℓo ℓh

f.obj cbidir c = dcBidir c

f.obj (df.f (f.hom cbidir cf)) = f.obj cf
f.hom (df.f (f.hom cbidir cf)) φ = (f.hom cf (prl φ)) , (f.hom cf (prr φ))
f.hom-id (df.f (f.hom cbidir cf)) x = ×ext (f.hom-id cf x) (f.hom-id cf x)
f.hom-m∘ (df.f (f.hom cbidir cf)) ψ φ = ×ext (f.hom-m∘ cf (prl ψ) (prl φ)) (f.hom-m∘ cf (prr φ) (prr ψ))
df.hom-† (f.hom cbidir cf) φ = refl

f.hom-id cbidir x = dfunctorext (functorext refl)

f.hom-m∘ cbidir ψ φ = dfunctorext (functorext refl)
