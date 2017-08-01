{-# OPTIONS --type-in-type #-}

module willow2.cat.Isomorphism where

open import willow2.cat.Category
open import willow2.cat.Opposite

record Iso (c : Cat) (x y : Obj c) : Set (ℓh c) where
  constructor iso
  field
    fwd : Hom c x y
    bck : Hom c y x
    .{{src-id}} : bck ∘ fwd ≡ id
    .{{tgt-id}} : fwd ∘ bck ≡ id
open Iso public

i-id⟨_⟩ : ∀{c} (x : Obj c) → Iso c x x
fwd i-id⟨ x ⟩ = id
bck i-id⟨ x ⟩ = id
src-id i-id⟨ x ⟩ = lunit _ 
tgt-id i-id⟨ x ⟩ = lunit _ 

_i∘_ : ∀{c} {x y z : Obj c} → (ψ : Iso c y z) → (φ : Iso c x y) → Iso c x z
fwd (ψ i∘ φ) = fwd ψ ∘ fwd φ
bck (ψ i∘ φ) = bck φ ∘ bck ψ
src-id (ψ i∘ φ) = begin
  (bck φ ∘ bck ψ) ∘ (fwd ψ ∘ fwd φ)
    ≡⟨ assoc _ _ _ ⟩
  bck φ ∘ (bck ψ ∘ (fwd ψ ∘ fwd φ))
    ≡⟨ cong (λ χ → _ ∘ χ) (sym (assoc _ _ _)) ⟩
  bck φ ∘ ((bck ψ ∘ fwd ψ) ∘ fwd φ)
    ≡⟨ cong (λ χ → _ ∘ (χ ∘ _)) (src-id ψ) ⟩
  bck φ ∘ (id ∘ fwd φ)
    ≡⟨ cong (λ χ → _ ∘ χ) (lunit _) ⟩
  bck φ ∘ fwd φ
    ≡⟨ src-id φ ⟩
  id ∎
tgt-id (ψ i∘ φ) = begin
  (fwd ψ ∘ fwd φ) ∘ (bck φ ∘ bck ψ)
    ≡⟨ assoc _ _ _ ⟩
  fwd ψ ∘ (fwd φ ∘ (bck φ ∘ bck ψ))
    ≡⟨ cong (λ χ → _ ∘ χ) (sym (assoc _ _ _)) ⟩
  fwd ψ ∘ ((fwd φ ∘ bck φ) ∘ bck ψ)
    ≡⟨ cong (λ χ → _ ∘ (χ ∘ _)) (tgt-id φ) ⟩
  fwd ψ ∘ (id ∘ bck ψ)
    ≡⟨ cong (λ χ → _ ∘ χ) (lunit _) ⟩
  fwd ψ ∘ bck ψ
    ≡⟨ tgt-id ψ ⟩
  id ∎

ext-≅ : ∀{c} {x y : Obj c} {φ ψ : Iso c x y} → (fwd φ ≡ fwd ψ) → (bck φ ≡ bck ψ) → φ ≡ ψ
ext-≅ refl refl = refl

cCore : Cat → Cat
ℓo (cCore c) = ℓo c
ℓh (cCore c) = ℓh c
Obj (cCore c) = Obj c
Hom (cCore c) x y = Iso c x y
IsCat.id⟨ isCat (cCore c) ⟩ x = i-id⟨ x ⟩
IsCat._∘_ (isCat (cCore c)) ψ φ = ψ i∘ φ
IsCat.assoc (isCat (cCore c)) ψ χ φ = ext-≅ (assoc _ _ _) (sym (assoc _ _ _))
IsCat.lunit (isCat (cCore c)) φ = ext-≅ (lunit _) (runit _)
IsCat.runit (isCat (cCore c)) φ = ext-≅ (runit _) (lunit _)

i-inv : ∀{c} {x y : Obj c} → Iso c x y → Iso c y x
fwd (i-inv φ) = bck φ
bck (i-inv φ) = fwd φ
src-id (i-inv φ) = tgt-id φ
tgt-id (i-inv φ) = src-id φ

i-inv²=id : ∀{c x y} {φ : Iso c x y} → i-inv (i-inv φ) ≡ φ
i-inv²=id = refl

c-inv-core : ∀{c} → (cOp (cCore c) c→ cCore c)
c-inv-core = ftr i-inv

c-inv-core²=c-id : ∀{c} → c-inv-core c∘ c-op c-inv-core ≡ c-id⟨ cCore c ⟩
c-inv-core²=c-id = refl
