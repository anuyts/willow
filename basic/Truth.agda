module aken.basic.Truth where

open import aken.basic.Levels

------------------------------

data ⊤ : Set where
  unit : ⊤

------------------------------

data ⊥ : Set lzero where
  --no constructors

quodlibet : {α : Level} -> {A : Set α} -> ⊥ -> A
quodlibet ()

Not : {α : Level} -> Set α -> Set _
Not A = A -> ⊥

--dquodlibet : ∀ {α} → (X : ⊥ → Set α) → (c : ⊥) → X c
--dquodlibet X ()
