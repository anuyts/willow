{-# OPTIONS --type-in-type #-}

module willow2.cat.FullyFaithfulSubcategory where

open import willow2.cat.Category

record FFSubHom {A : Set} (cB : Cat) (f : A → Obj cB) (x y : A) : Set where
  constructor ffSubHom
  field
    runFFSubHom : Hom cB (f x) (f y)
open FFSubHom public

cFFSub : ∀{ℓA} {A : Set ℓA} (cB : Cat) (f : A → Obj cB) → Cat
ℓo (cFFSub {ℓA} cB f) = ℓA
ℓh (cFFSub cB f) = ℓh cB
Obj (cFFSub {_}{A} cB f) = A
Hom (cFFSub cB f) = FFSubHom cB f
IsCat.id⟨_⟩ (isCat (cFFSub cB f)) x = ffSubHom id
IsCat._∘_ (isCat (cFFSub cB f)) (ffSubHom χ) (ffSubHom φ) = ffSubHom (χ ∘ φ)
IsCat.assoc (isCat (cFFSub cB f)) (ffSubHom ψ) (ffSubHom χ) (ffSubHom φ) = cong ffSubHom (assoc ψ χ φ)
IsCat.lunit (isCat (cFFSub cB f)) (ffSubHom φ) = cong ffSubHom (lunit φ)
IsCat.runit (isCat (cFFSub cB f)) (ffSubHom φ) = cong ffSubHom (runit φ)

c-ff-incl : ∀{ℓA} {A : Set ℓA} (cB : Cat) (f : A → Obj cB) → (cFFSub cB f c→ cB)
obj (c-ff-incl cB f) = f
hom (c-ff-incl cB f) = runFFSubHom
hom-id (c-ff-incl cB f) = refl
hom-comp (c-ff-incl cB f) ψ φ = refl
