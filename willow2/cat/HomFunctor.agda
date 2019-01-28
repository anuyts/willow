{-# OPTIONS --type-in-type --irrelevant-projections #-}

module willow2.cat.HomFunctor where

open import willow2.cat.Category
open import willow2.cat.Product public
open import willow2.cat.Opposite public
open import willow2.cat.OfSets public

c-hom : ∀(cA : Cat) → (cOp cA c× cA c→ cSet (ℓh cA))
obj (c-hom cA) (a , b) = Hom cA a b
hom (c-hom cA) (φ1 , φ3) φ2 = φ3 ∘ (φ2 ∘ φ1)
hom-id (c-hom cA) = λ= φ , trans (lunit _) (runit _)
hom-comp (c-hom cA) (φ1 , φ5) (φ2 , φ4) = λ= φ3 , (begin
  (φ5 ∘ φ4) ∘ (φ3 ∘ (φ2 ∘ φ1))
    ≡⟨ assoc _ _ _ ⟩
  φ5 ∘ (φ4 ∘ (φ3 ∘ (φ2 ∘ φ1)))
    ≡⟨ cong (λ ψ → _ ∘ (_ ∘ ψ)) (sym (assoc _ _ _)) ⟩
  φ5 ∘ (φ4 ∘ ((φ3 ∘ φ2) ∘ φ1))
    ≡⟨ cong (λ ψ → _ ∘ ψ) (sym (assoc _ _ _)) ⟩
  φ5 ∘ ((φ4 ∘ (φ3 ∘ φ2)) ∘ φ1) ∎)
