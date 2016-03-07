module aken.basic.Naturals where

open import aken.basic.Levels

data Nat : Set lzero where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
--{-# BUILTIN SUC suc #-}
--{-# BUILTIN ZERO zero #-}

_+_ : Nat -> Nat -> Nat
zero + n = n
(suc m) + n = suc (m + n)

add_to_ : Nat → Nat → Nat
add_to_ = _+_


data _≤_ : Nat → Nat → Set lzero where
  ≤refl : {n : Nat} → n ≤ n
  ≤incr : {m n : Nat} → m ≤ n → m ≤ (suc n)

data _<_ : Nat → Nat → Set lzero where
  <suc : {n : Nat} → n < (suc n)
  <incr : {m n : Nat} → m < n → m < (suc n)

infix 1 _<_ _≤_
