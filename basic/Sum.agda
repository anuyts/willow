module aken.basic.Sum where

open import aken.basic.Levels
open import aken.basic.Identity

--\sum
record ∑ {α β} (A : Set α) (B : A -> Set β) : Set (α ⊔ β) where
  constructor _,_ -- : (a : A) -> (b : B a) -> Sum B
  field
    prl : A
    prr : B prl
open ∑ public

Sum : ∀{α β} → {A : Set α} → (B : A → Set β) → Set (α ⊔ β)
Sum B = ∑ _ B

infixr 5 _,_

_×_ : {α β : Level} -> (A : Set α) -> (B : Set β) -> Set (α ⊔ β)
A × B = ∑ A (λ _ -> B)

_&_ : {α β : Level} -> {A : Set α} -> {B : Set β} -> A → B → A × B
a & b = a , b

_AND_ = _×_

infixr 4 _×_
infixr 4 _AND_
infixr 5 _&_

--identity of pairs-------------------

pair-ext : ∀{α β} → {A : Set α} → {B : A → Set β}
  → {a a' : A} → (p : a == a')
  → {b : B a} → {b' : B a'} → (q : (tra B / p of b) == b')
  → (a , b) == (a' , b')
pair-ext {_}{_} {A}{B} {a}{.a} refl {b}{.b} refl = refl

×ext : ∀{ℓL ℓR} → {L : Set ℓL} → {R : Set ℓR}
  → {l l' : L} → (p : l == l')
  → {r r' : R} → (q : r == r')
  → (l , r) == (l' , r')
×ext refl refl = refl

--handy stuff------------------------

×intro : ∀{ℓA ℓL ℓR} → {A : Set ℓA} → {L : Set ℓL} → {R : Set ℓR} → (f : A → L) → (g : A → R) → A → L × R
×intro f g a = f a , g a

_⊠_ = ×intro

map× : ∀{ℓL ℓL' ℓR ℓR'}
  → {L : Set ℓL} → {L' : Set ℓL'} → {R : Set ℓR} → {R' : Set ℓR'}
  → (f : L → L') → (g : R → R') → (L × R → L' × R')
map× f g lr = f (prl lr) , g (prr lr)
