module willow.util.IdxSet where

open import willow.basic.Levels public
open import willow.basic.Coproduct public
open import willow.basic.Truth public
open import willow.basic.Sum public
open import willow.basic.Identity public

record IdxSet {ℓA : Level} (ℓ : Level) (A : Set ℓA) : Set (lsuc ℓ ⊔ ℓA) where
  constructor ℑ
  field
    Idx : Set ℓ
    val : Idx → A
module ℑ = IdxSet --\Im

_ℑ+_ : ∀{ℓX ℓY ℓA} → {A : Set ℓA} → (ℑX : IdxSet ℓX A) → (ℑY : IdxSet ℓY A) → IdxSet (ℓX ⊔ ℓY) A
IdxSet.Idx (ℑX ℑ+ ℑY) = ℑ.Idx ℑX OR ℑ.Idx ℑY
IdxSet.val (ℑX ℑ+ ℑY) (inl i) = ℑ.val ℑX i
IdxSet.val (ℑX ℑ+ ℑY) (inr j) = ℑ.val ℑY j

ℑ⊥ : ∀{ℓA} → {A : Set ℓA} → IdxSet lzero A
IdxSet.Idx ℑ⊥ = ⊥
IdxSet.val ℑ⊥ ()

ℑ⊤ : ∀{ℓA} → {A : Set ℓA} → A → IdxSet lzero A
IdxSet.Idx (ℑ⊤ a) = ⊤
IdxSet.val (ℑ⊤ a) i = a

ℑkill : ∀{ℓX ℓA} → {A : Set ℓA} → (ℑX : IdxSet ℓX A) → (i : ℑ.Idx ℑX) → IdxSet ℓX A
IdxSet.Idx (ℑkill ℑX i) = Sum λ(j : ℑ.Idx ℑX) → (j == i) → ⊥
IdxSet.val (ℑkill ℑX i) (j , p) = ℑ.val ℑX j
