module willow2.basic.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public

_$_≡_ : ∀{ℓ} → (A : Set ℓ) → A → A → Set ℓ
A $ a ≡ b = a ≡ b
