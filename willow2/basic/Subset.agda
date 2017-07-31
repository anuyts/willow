module willow2.basic.Subset where

open import Level
open import Relation.Binary.PropositionalEquality

record Subset {ℓA ℓP} (A : Set ℓA) (P : A → Set ℓP) : Set (ℓA ⊔ ℓP) where
  constructor _,_
  field
    get : A
    .wit : P get
open Subset public

syntax Subset A (λ x → P) = [ x ∈ A ! P ]

ext-Subset : ∀ {ℓA ℓP} {A : Set ℓA} {P : A → Set ℓP} {x y : [ a ∈ A ! P a ]} → get x ≡ get y → x ≡ y
ext-Subset {x = .(get y) , px} {y} refl = refl
