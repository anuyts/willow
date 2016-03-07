module aken.basic.UIP where

open import aken.basic.Basic public
open import aken.basic.Propositional public

postulate uip : ∀{α} → {A : Set α} → {a b : A} → Is¶ (a == b)
