module willow.basic.Basic where

open import willow.basic.Levels public
open import willow.basic.Identity public
open import willow.basic.Truth public
open import willow.basic.Booleans public
open import willow.basic.Naturals public
open import willow.basic.Coproduct public
open import willow.basic.List public
open import willow.basic.Fin public
open import willow.basic.Vector public
open import willow.basic.Sum public

--PROOF-TOOLS-------------------

_besides_ : ∀ {α β} {A : Set α} {B : Set β} -> A -> B -> A
a besides b = a

infix 0 _besides_

--annotating--------------------------

_∋_ : ∀{α} → (A : Set α) → A → A
A ∋ a = a

infix 0 _∋_
