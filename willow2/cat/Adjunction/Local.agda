{-# OPTIONS --type-in-type #-}

module willow2.cat.Adjunction.Local where

open import willow2.cat.Category
open import willow2.cat.Isomorphism public
open import willow2.cat.Exponential public
open import willow2.cat.OfSets public
open import willow2.cat.HomFunctor public

record [_↦_]⊣_ {cA cB : Cat} (a : Obj cA) (la : Obj cB) (cr : cB c→ cA) : Set ℓ? where
  constructor pv-left-adj
  field
    pf-left-adj : Iso (cExp cB (cSet ℓ?))
                      (c-hom cB c∘ (c-const {_} {cOp cB} la c, c-id))
                      (c-hom cA c∘ (c-const {_} {cOp cA} a c, cr))

record _⊣[_↦_] {cA cB : Cat} (cl : cA c→ cB) (b : Obj cB) (rb : Obj cA) : Set ℓ? where
  field
    pf-right-adj : Iso (cExp (cOp cA) (cSet ℓ?))
                       (c-hom cB c∘ (c-op cl c, c-const {_} {cB} b))
                       (c-hom cA c∘ (c-id c, c-const {_} {cA} rb))

{-
_⊣[_↦_] : ∀ {cA cB : Cat} (cl : cA c→ cB) (b : Obj cB) (rb : Obj cA) → Set ℓ?
cl ⊣[ b ↦ rb ] = [ b ↦ rb ]⊣ c-op cl

pv-right-adj : ∀ {cA cB : Cat} {cl : cA c→ cB} {b : Obj cB} {rb : Obj cA} →
             Iso (cExp (cOp cA) (cSet ℓ?))
                       (c-hom cB c∘ (c-op cl c, c-const {_} {cB} b))
                       (c-hom cA c∘ (c-id c, c-const {_} {cA} rb)) → cl ⊣[ b ↦ rb ]
pv-right-adj {cA}{cB}{cl}{b}{rb} i-nt = pv-left-adj {!!}
-}
