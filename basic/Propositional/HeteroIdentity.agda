module willow.basic.Propositional.HeteroIdentity where

open import willow.basic.Propositional
open import willow.basic.Identity
open import willow.basic.Sum

data _,_$_===_ {ℓ} : (A B : Set ℓ) → (a : A) → (b : B) → Set ℓ where
  hrefl : {A : Set ℓ} → {a : A} → A , A $ a === a

_===_ : ∀{ℓ} → {A B : Set ℓ} → A → B → Set ℓ
a === b = _ , _ $ a === b

infix 1 _===_

_h•_ : ∀ {ℓ} → {A B C : Set ℓ} → {a : A} {b : B} {c : C} → (a === b) → (b === c) → (a === c)
hrefl h• hrefl = hrefl

infixl 10 _h•_

to-heter : ∀{ℓ} {A : Set ℓ} {a b : A} (p : a == b) → (a === b)
to-heter refl = hrefl

--Critically uses K!
to-homog : ∀{ℓ} {A : Set ℓ} {a b : A} (p : a === b) → (a == b)
to-homog hrefl = refl

via_$_h•_ : ∀ {ℓ} → {A B C : Set ℓ} → {a : A} {c : C} → (b : B) → (a === b) → (b === c) → (a === c)
via _ $ hrefl h• hrefl = hrefl

hsym : ∀{α} → {A B : Set α} → {a : A} → {b : B} → (a === b) → (b === a)
hsym hrefl = hrefl

htransport : ∀{α β} → {A : Set α} → {a a' : A} → (B : A → Set β) → (p : a == a') → (b : B a) → (tra B / p of b === b)
htransport B refl b = hrefl

htra_/_of_ = htransport
htra_/_ = htransport

pair-hext : ∀{α β} → {A : Set α} → {B : A → Set β}
  → {a a' : A} → (p : a == a')
  → {b : B a} → {b' : B a'} → (q : b === b')
  → (a , b) == (a' , b')
pair-hext {_}{_} {A}{B} {a}{.a} refl {b}{.b} hrefl = refl
