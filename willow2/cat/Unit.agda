{-# OPTIONS --type-in-type #-}

module willow2.cat.Unit where

open import willow2.cat.Category
open import Data.Unit

c⊤ : Cat
ℓo c⊤ = zero
ℓh c⊤ = zero
Obj c⊤ = ⊤
Hom c⊤ _ _ = ⊤
IsCat.id⟨ isCat c⊤ ⟩ _ = tt
IsCat._∘_ (isCat c⊤) _ _ = tt
IsCat.assoc (isCat c⊤) ψ ξ φ = refl
IsCat.lunit (isCat c⊤) φ = refl
IsCat.runit (isCat c⊤) φ = refl

c-tt : ∀{cA} → (cA c→ c⊤)
c-tt = c-const tt
