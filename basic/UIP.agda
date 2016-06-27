module willow.basic.UIP where

open import willow.basic.Basic public
open import willow.basic.Propositional public

uip : ∀{α} → {A : Set α} → {a b : A} → Is¶ (a == b)
uip {ℓ}{A}{a}{.a}{refl}{refl}= refl
