module willow.basic.UIP where

open import willow.basic.Basic public
open import willow.basic.Propositional public

postulate uip : ∀{α} → {A : Set α} → {a b : A} → Is¶ (a == b)
