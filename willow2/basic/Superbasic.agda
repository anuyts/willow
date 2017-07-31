module willow2.basic.Superbasic where

_∋_ : ∀{ℓ} → (A : Set ℓ) → A → A
A ∋ a = a

fetch : ∀{ℓ} {A : Set ℓ} → {{a : A}} → A
fetch {{a}} = a
