module willow.basic.Levels where

open import Agda.Primitive public

record Lift {ℓ↓ ℓ↑} (A : Set ℓ↓) : Set (ℓ↓ ⊔ ℓ↑) where
  constructor lift
  field lower : A
open Lift public
