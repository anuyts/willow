{-# OPTIONS --type-in-type #-}

module willow2.cat.Opposite where

open import willow2.cat.Category

{-
{-# BUILTIN REWRITE _≡_ #-}

abstract
  Op : ∀{ℓ} → Set ℓ → Set ℓ
  Op A = A
  Op²=Id : ∀{ℓ} → (A : Set ℓ) → Op (Op A) ≡ A
  Op²=Id A = refl

{-# REWRITE Op²=Id #-}
-}

--beware of instance-related confusion!
cOp : Cat → Cat
ℓo (cOp c) = ℓo c
ℓh (cOp c) = ℓh c
Obj (cOp c) = Obj c
Hom (cOp c) x y = Hom c y x
IsCat.id-at (isCat (cOp c)) x = id
IsCat._∘_ (isCat (cOp c)) ψ φ = φ ∘ ψ
IsCat.assoc (isCat (cOp c)) ψ ξ φ = sym (assoc φ ξ ψ)
IsCat.lunit (isCat (cOp c)) φ = runit φ
IsCat.runit (isCat (cOp c)) φ = lunit φ
