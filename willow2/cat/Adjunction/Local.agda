{-# OPTIONS --type-in-type #-}

module willow2.cat.Adjunction.Local where

open import willow2.cat.Category
open import willow2.cat.Isomorphism public
open import willow2.cat.Exponential public
open import willow2.cat.OfSets public
open import willow2.cat.HomFunctor public

record [_↦_]⊣_ {cA cB : Cat} (a : Obj cA) (la : Obj cB) (cr : cB c→ cA) : Set ℓ? where
  field
    loc-left-adj : Iso (cExp cB (cSet ℓ?))
                       (c-hom cB c∘ (c-const {_} {cOp cB} la c, c-id))
                       (c-hom cA c∘ (c-const {_} {cOp cA} a c, cr))
