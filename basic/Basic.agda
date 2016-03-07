module aken.basic.Basic where

open import aken.basic.Levels public
open import aken.basic.Identity public
open import aken.basic.Truth public
open import aken.basic.Booleans public
open import aken.basic.Naturals public
open import aken.basic.Coproduct public
open import aken.basic.List public
open import aken.basic.Fin public
open import aken.basic.Vector public
open import aken.basic.Sum public

--PROOF-TOOLS-------------------

_besides_ : ∀ {α β} {A : Set α} {B : Set β} -> A -> B -> A
a besides b = a

infix 0 _besides_

--annotating--------------------------

_∋_ : ∀{α} → (A : Set α) → A → A
A ∋ a = a

infix 0 _∋_
