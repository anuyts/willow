module willow.util.IdxSet where

open import willow.basic.Levels public
open import willow.basic.Coproduct public
open import willow.basic.Truth public
open import willow.basic.Sum public
open import willow.basic.Identity public
open import willow.basic.Function public
open import willow.basic.UIP public
open import willow.cat.Sets public

record IdxSet {ℓA : Level} (ℓ : Level) (A : Set ℓA) : Set (lsuc ℓ ⊔ ℓA) where
  no-eta-equality
  constructor ℑ
  field
    Idx : Set ℓ
    val : Idx → A
module ℑ = IdxSet --\Im

_ℑ+_ : ∀{ℓX ℓY ℓA} → {A : Set ℓA} → (ℑX : IdxSet ℓX A) → (ℑY : IdxSet ℓY A) → IdxSet (ℓX ⊔ ℓY) A
IdxSet.Idx (ℑX ℑ+ ℑY) = ℑ.Idx ℑX OR ℑ.Idx ℑY
IdxSet.val (ℑX ℑ+ ℑY) (inl i) = ℑ.val ℑX i
IdxSet.val (ℑX ℑ+ ℑY) (inr j) = ℑ.val ℑY j

infix 3 _ℑ+_

ℑ⊥ : ∀{ℓA} → {A : Set ℓA} → IdxSet lzero A
IdxSet.Idx ℑ⊥ = ⊥
IdxSet.val ℑ⊥ ()

ℑ⊤ : ∀{ℓA} → {A : Set ℓA} → A → IdxSet lzero A
IdxSet.Idx (ℑ⊤ a) = ⊤
IdxSet.val (ℑ⊤ a) i = a

ℑkill : ∀{ℓX ℓA} → {A : Set ℓA} → (ℑX : IdxSet ℓX A) → (i : ℑ.Idx ℑX) → IdxSet ℓX A
IdxSet.Idx (ℑkill ℑX i) = Sum λ(j : ℑ.Idx ℑX) → (j == i) → ⊥
IdxSet.val (ℑkill ℑX i) (j , p) = ℑ.val ℑX j

record _ℑ↠_ {ℓX ℓY ℓA} {A : Set ℓA} (X : IdxSet ℓX A) (Y : IdxSet ℓY A) : Set (ℓX ⊔ ℓY ⊔ ℓA) where
  no-eta-equality
  constructor mkℑ↠
  field
    idx : ℑ.Idx X → ℑ.Idx Y
    val : ∀{i} → (ℑ.val X i == ℑ.val Y (idx i))
module ℑ↠ = _ℑ↠_

ℑ↠ext : ∀{ℓX ℓY ℓA} {A : Set ℓA} {ℑX : IdxSet ℓX A} {ℑY : IdxSet ℓY A} (φ ψ : ℑX ℑ↠ ℑY) (p : ℑ↠.idx φ == ℑ↠.idx ψ)
  → (φ == ψ)
ℑ↠ext (mkℑ↠ f r) (mkℑ↠ .f s) refl = map= (mkℑ↠ f) (λi= i => uip)

cIdxSet : ∀{ℓA} → (ℓ : Level) → (A : Set ℓA) → Cat (lsuc ℓ ⊔ ℓA) (ℓ ⊔ ℓA)
Cat.Obj (cIdxSet ℓ A) = IdxSet ℓ A
Cat.Hom (cIdxSet ℓ A) ℑX ℑY = ℑX ℑ↠ ℑY
ℑ↠.idx (Cat.id (cIdxSet ℓ A) ℑX) = idf
ℑ↠.val (Cat.id (cIdxSet ℓ A) ℑX) = refl
ℑ↠.idx (Cat.comp (cIdxSet ℓ A) ψ φ) = ℑ↠.idx ψ ∘ ℑ↠.idx φ
ℑ↠.val (Cat.comp (cIdxSet ℓ A) ψ φ) = ℑ↠.val φ • ℑ↠.val ψ
Cat.m∘assoc' (cIdxSet ℓ A) {w} {x} {y} {z} {φ} {ξ} {ψ} = ℑ↠ext _ _ (∘assoc (ℑ↠.idx ψ) (ℑ↠.idx ξ) (ℑ↠.idx φ))
Cat.m∘lunit' (cIdxSet ℓ A) = ℑ↠ext _ _ refl
Cat.m∘runit' (cIdxSet ℓ A) = ℑ↠ext _ _ refl

infix 2 _ℑ↠_
