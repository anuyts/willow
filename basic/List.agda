module aken.basic.List where

data List {ξ} (X : Set ξ) : Set ξ where
  [] : List X
  _::_ : X -> List X -> List X

infixr 5 _::_

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}
