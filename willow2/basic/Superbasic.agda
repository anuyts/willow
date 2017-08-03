module willow2.basic.Superbasic where

fetch : ∀{ℓ} {A : Set ℓ} → {{a : A}} → A
fetch {{a}} = a

instap : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} → ({{x : A}} → B x) → (a : A) → B a
instap f a = f {{a}}
