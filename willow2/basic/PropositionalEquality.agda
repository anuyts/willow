{-# OPTIONS --rewriting #-}

module willow2.basic.PropositionalEquality where

open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import willow2.basic.Squash public

{-# BUILTIN REWRITE _≡_ #-}

open ≡-Reasoning hiding (_≅⟨_⟩_) public

[_∋_≡_] : ∀{ℓ} → (A : Set ℓ) → A → A → Set ℓ
[ A ∋ a ≡ b ] = a ≡ b
{-# DISPLAY _≡_ {_} {A} a b = [ A ∋ a ≡ b ] #-}

postulate
  instance ≡choice : ∀{ℓ}{A : Set ℓ}{a b : A} → Choice (a ≡ b)

postulate
  injΠ-dom : ∀{ℓA ℓB} {A A' : Set ℓA} {B : A → Set ℓB} {B' : A' → Set ℓB}
    → ((x : A) → B x) ≡ ((x' : A') → B' x') → A ≡ A'

_!>_ : ∀{ℓ} {A B : Set ℓ} → A → .(A ≡ B) → B
a !> e with choose e
a !> e | refl = a
{-
tra_along_ : ∀{ℓ} {A B : Set ℓ} → A → .(A ≡ B) → B
tra a along e with choose e
tra a along e | refl = a
-}
infixl 10 _!>_

open import Data.Product
ext-× : ∀{ℓA ℓB} {A : Set ℓA} {B : Set ℓB} {p q : A × B} → proj₁ p ≡ proj₁ q → proj₂ p ≡ proj₂ q → p ≡ q
ext-× refl refl = refl
