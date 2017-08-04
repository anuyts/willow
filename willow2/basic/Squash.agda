module willow2.basic.Squash where

record Squash {ℓ} (A : Set ℓ) : Set ℓ where
  instance
    constructor squash
  field
    .unsquash : A
open Squash public

record Choice {ℓ} (A : Set ℓ) : Set ℓ where
  field
    choose : .A → A
open Choice {{...}} public

{-# DISPLAY Choice.choose c x = choose {{c}} x #-}
