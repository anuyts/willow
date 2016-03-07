module willow.basic.Fin where

open import willow.basic.Naturals public
open import willow.basic.Truth public
open import willow.basic.Coproduct public

data Fin : (n : Nat) -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

flift : {n : Nat} → Fin n → Fin (suc n)
flift fzero = fzero
flift (fsuc m) = fsuc (flift m)

Finrec : Nat → Set
Finrec zero = ⊥
Finrec (suc n) = (Finrec n) OR ⊤

finrec2nat : {n : Nat} → Finrec n → Nat
finrec2nat {zero} k = quodlibet k
finrec2nat {suc n} (inr x) = 0
finrec2nat {suc n} (inl x) = suc (finrec2nat x)
