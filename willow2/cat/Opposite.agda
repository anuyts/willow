{-# OPTIONS --type-in-type --irrelevant-projections #-}

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
IsCat.id⟨_⟩ (isCat (cOp c)) x = id
IsCat._∘_ (isCat (cOp c)) ψ φ = φ ∘ ψ
IsCat.assoc (isCat (cOp c)) ψ ξ φ = sym (assoc φ ξ ψ)
IsCat.lunit (isCat (cOp c)) φ = runit φ
IsCat.runit (isCat (cOp c)) φ = lunit φ

cOp²=id : ∀{cA} → cOp (cOp cA) ≡ cA
cOp²=id = refl

c-op : ∀{cA cB} → (cA c→ cB) → (cOp cA c→ cOp cB)
obj (c-op {cA} {cB} cf) = obj cf
hom (c-op {cA} {cB} cf) = hom cf
hom-id (c-op {cA} {cB} cf) = hom-id cf
hom-comp (c-op {cA} {cB} cf) ψ φ = hom-comp cf φ ψ

c-op²=id : ∀{cA cB} {cf : cA c→ cB} → c-op (c-op cf) ≡ cf
c-op²=id = refl
