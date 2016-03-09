module willow.basic.Booleans where

data Bool : Set where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

not : Bool -> Bool
not true = false
not false = true
