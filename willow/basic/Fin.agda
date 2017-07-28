module willow.basic.Fin where

open import willow.basic.Naturals public
open import willow.basic.Truth public
open import willow.basic.Coproduct public
open import willow.basic.Function public

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

outFinrec+ : {m n : Nat} → Finrec (add n to m) → (Finrec m) OR (Finrec n)
outFinrec+ {m}{zero} i = inl i
outFinrec+ {m}{suc n} (inr unit) = inr (inr unit)
outFinrec+ {m}{suc n} (inl i) = mapOR idf inl (outFinrec+ {m}{n} i)

inlFinrec+ : {m n : Nat} → (Finrec m) → Finrec (add n to m)
inlFinrec+ {m}{zero} = idf
inlFinrec+ {m}{suc n} = inl ∘ (inlFinrec+ {m}{n})

inrFinrec+ : {m n : Nat} → (Finrec n) → Finrec (add n to m)
inrFinrec+ {m}{zero} ()
inrFinrec+ {m}{suc n} (inl j) = inl (inrFinrec+ {m}{n} j)
inrFinrec+ {m}{suc n} (inr unit) = inr unit
