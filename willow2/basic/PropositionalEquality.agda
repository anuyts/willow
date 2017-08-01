module willow2.basic.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public

_$_≡_ : ∀{ℓ} → (A : Set ℓ) → A → A → Set ℓ
A $ a ≡ b = a ≡ b

open import Data.Product
ext-× : ∀{ℓA ℓB} {A : Set ℓA} {B : Set ℓB} {p q : A × B} → proj₁ p ≡ proj₁ q → proj₂ p ≡ proj₂ q → p ≡ q
ext-× refl refl = refl
