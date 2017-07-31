module willow2.basic.Squash where

record Squash {ℓ} (A : Set ℓ) : Set ℓ where
  instance
    constructor squash
  field
    .unsquash : A
open Squash public
