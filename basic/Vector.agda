module willow.basic.Vector where

open import willow.basic.Naturals
open import willow.basic.Fin

data Vector {ξ} (X : Set ξ) : (n : Nat) -> Set ξ where
  v[] : Vector X 0
  _v::_ : {n : Nat} -> (x : X) -> (xs : Vector X n) -> Vector X (suc n)

infixr 5 _v::_

_[_] : {X : Set} -> {n : Nat} -> Vector X n -> Fin n -> X
(x v:: xs) [ fzero ] = x
(x v:: xs) [ fsuc n ] = xs [ n ]
