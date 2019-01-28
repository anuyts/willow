module willow2.basic.Funext where

open import willow2.basic.PropositionalEquality
open import willow2.basic.HeterogeneousEquality

postulate
  --instance
    funext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} (e : (a : A) → f a ≡ g a) → f ≡ g
    funexti : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : {a : A} → B a} (e : (a : A) → f {a} ≡ g {a})
      → [({a : A} → B a) ∋ f ≡ g ]
    funext≅ : ∀{ℓA ℓB} {A : Set ℓA} {B B' : A → Set ℓB} {f : (a : A) → B a} {g : (a : A) → B' a}
      → (e : (a : A) → f a ≅ g a) → f ≅ g

syntax funext (λ x → e) = λ= x , e
syntax funexti (λ x → e) = λ=[ x ], e
syntax funext≅ (λ x → e) = λ≅ x , e
