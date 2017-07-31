module willow2.basic.Superbasic where

fetch : ∀{ℓ} {A : Set ℓ} → {{a : A}} → A
fetch {{a}} = a
