{-# OPTIONS --type-in-type #-}

module willow2.cat.Exponential where

open import willow2.cat.Category

cExp : Cat → Cat → Cat
ℓo (cExp cA cB) = ℓo cA ⊔ ℓh cA ⊔ ℓo cB ⊔ ℓh cB
ℓh (cExp cA cB) = ℓ?
Obj (cExp cA cB) = cA c→ cB
Hom (cExp cA cB) cf cg = cf nt→ cg
IsCat.id-at (isCat (cExp cA cB)) cf = nt-id
IsCat._∘_ (isCat (cExp cA cB)) ntb nta = ntb nt∘ nta
IsCat.assoc (isCat (cExp cA cB)) ntc ntb nta = ext-nt (λ= a , assoc _ _ _)
IsCat.lunit (isCat (cExp cA cB)) nta = ext-nt (λ= a , lunit _)
IsCat.runit (isCat (cExp cA cB)) nta = ext-nt (λ= a , runit _)
