{-# OPTIONS --type-in-type #-}

module willow2.cat.Empty where

open import willow2.cat.Category
open import Data.Empty

c⊥ : Cat
ℓo c⊥ = zero
ℓh c⊥ = zero
Obj c⊥ = ⊥
Hom c⊥ x y = ⊥
IsCat.id⟨ isCat c⊥ ⟩ ()
IsCat._∘_ (isCat c⊥) {}
IsCat.assoc (isCat c⊥) {}
IsCat.lunit (isCat c⊥) {}
IsCat.runit (isCat c⊥) {}

c-absurd : ∀{cA} → (c⊥ c→ cA)
obj c-absurd ()
hom c-absurd {}
hom-id c-absurd {}
hom-comp c-absurd {}
