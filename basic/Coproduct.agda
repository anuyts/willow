module aken.basic.Coproduct where

open import aken.basic.Levels

data _OR_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
  inl : (a : A) -> A OR B
  inr : (b : B) -> A OR B

infixl 4 _OR_
