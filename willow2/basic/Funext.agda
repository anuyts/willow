module willow2.basic.Funext where

open import willow2.basic.PropositionalEquality

postulate
  funext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} (e : (a : A) → f a ≡ g a) → f ≡ g
  funexti : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : {a : A} → B a} (e : (a : A) → f {a} ≡ g {a})
    → [({a : A} → B a) ∋ f ≡ g ]

instance
  instfunext : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : (a : A) → B a} {{e : (a : A) → f a ≡ g a}} → f ≡ g
  instfunext {{e}} = funext e
  instfunexti : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : {a : A} → B a} {{e : (a : A) → f {a} ≡ g {a}}}
    → [({a : A} → B a) ∋ f ≡ g ]
  instfunexti {{e}} = funexti e

syntax funext (λ x → e) = λ= x , e
syntax funexti (λ x → e) = λ=[ x ], e
