module willow.cat.HomFunctor where

open import willow.cat.Category public
open import willow.cat.Product public
open import willow.cat.Opposite public
open import willow.cat.Sets public

cHom : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → ((cOp c c× c) ++> cSet ℓh)
cHom {ℓo}{ℓh} c = record
  { obj = λ xs → c.Hom c (prl xs) (prr xs)
  ; hom = λ φs ξ → c $ (c $ prr φs m∘ ξ) m∘ prl φs
  ; hom-id = λ x → λ= ξ => (c.m∘runit c • c.m∘lunit c)
  ; hom-m∘ = λ ψs φs → λ= ξ => (
      map= (λ θ → c $ θ m∘ (c $ prl φs m∘ prl ψs)) (c.m∘assoc c) •
      sym (c.m∘assoc c) •
      map= (λ θ → c $ θ m∘ prl ψs) (c.m∘assoc c)
    )
  }
