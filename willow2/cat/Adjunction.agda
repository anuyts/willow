{-# OPTIONS --type-in-type #-}

module willow2.cat.Adjunction where

open import willow2.cat.Category
open import willow2.cat.Isomorphism public
open import willow2.cat.Exponential public
open import willow2.cat.OfSets public
open import willow2.cat.HomFunctor public

module Global where
  record _⊣_ {cA cB : Cat} (cl : cA c→ cB) (cr : cB c→ cA) : Set ℓ? where
    field
      η : c-id nt→ cr c∘ cl
      ε : cl c∘ cr nt→ c-id
      .{{ηr∘rε}} : (η nt⊚ nt-id⟨ cr ⟩) nt∘ (nt-id⟨ cr ⟩ nt⊚ ε) ≡ nt-id⟨ (cr c∘ cl) c∘ cr ⟩
      .{{lη∘ηl}} : (nt-id⟨ cl ⟩ nt⊚ η) nt∘ (ε nt⊚ nt-id⟨ cl ⟩) ≡ nt-id⟨ (cl c∘ cr) c∘ cl ⟩

module Local where
  record [_↦_]⊣_ {cA cB : Cat} (a : Obj cA) (la : Obj cB) (cr : cB c→ cA) : Set ℓ? where
    field
      loc-left-adj : Iso (cExp cB (cSet ℓ?))
                         (c-hom cB c∘ (c-const {_} {cOp cB} la c, c-id))
                         (c-hom cA c∘ (c-const {_} {cOp cA} a c, cr))
