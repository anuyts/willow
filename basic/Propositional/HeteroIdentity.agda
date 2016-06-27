module willow.basic.Propositional.HeteroIdentity where

open import willow.basic.Propositional
open import willow.basic.Identity
open import willow.basic.Sum
open import willow.basic.Function

data _$_===_ {ℓ} : {A B : Set ℓ} → (p : A == B) → (a : A) → (b : B) → Set ℓ where
  hrefl : {A : Set ℓ} → {a : A} → refl $ a === a
  
infix 1 _$_===_

_===_ : ∀{ℓ} → {A B : Set ℓ} {P : A == B} → A → B → Set ℓ
_===_ {P = P} a b = P $ a === b

infix 1 _===_

_h•_ : ∀ {ℓ} → {A B C : Set ℓ} {p : A == B} {q : B == C}
  → {a : A} {b : B} {c : C} → (p $ a === b) → (q $ b === c) → ((p • q) $ a === c)
hrefl h• hrefl = hrefl

infixl 10 _h•_

to-heter : ∀{ℓ} {A : Set ℓ} {a b : A} (p : a == b) → (refl $ a === b)
to-heter refl = hrefl

--Critically uses K!
to-homog : ∀{ℓ} {A : Set ℓ} {P : A == A} {a b : A} (p : P $ a === b) → (a == b)
to-homog hrefl = refl

via_$_h•_ : ∀ {ℓ} → {A B C : Set ℓ} {P : A == B} {Q : B == C}
  → {a : A} {c : C} → (b : B) → (P $ a === b) → (Q $ b === c) → (P • Q $ a === c)
via _ $ hrefl h• hrefl = hrefl

hsym : ∀{α} → {A B : Set α} {P : A == B} → {a : A} → {b : B} → (P $ a === b) → (sym P $ b === a)
hsym hrefl = hrefl

htransport : ∀{α β} → {A : Set α} → {a a' : A} → (B : A → Set β) → (p : a == a') → (b : B a) → (sym (map= B p) $ tra B / p of b === b)
htransport B refl b = hrefl

htra_/_of_ = htransport
htra_/_ = htransport

htra! : ∀{ℓ} → {A B : Set ℓ} → (p : A == B) → (a : A) → sym p $ tra! p a === a
htra! refl a = hrefl

pair-hext : ∀{α β} → {A : Set α} → {B : A → Set β}
  → {a a' : A} → (p : a == a')
  → {b : B a} → {b' : B a'} → (q : map= B p $ b === b')
  → (a , b) == (a' , b')
pair-hext {_}{_} {A}{B} {a}{.a} refl {b}{.b} hrefl = refl

comp-hlemma : ∀{ℓA ℓB ℓC} → {A A' : Set ℓA} {P : A == A'} → {B B' : Set ℓB} {Q : B == B'} → {C C' : Set ℓC} {R : C == C'}
  → {f : A → B} → {f' : A' → B'} → (p : (map= Fun P) =ap= Q $ f === f')
  → {g : B → C} → {g' : B' → C'} → (q : (map= Fun Q) =ap= R $ g === g')
  → ((map= Fun P) =ap= R $ g ∘ f === g' ∘ f')
comp-hlemma {A = A}{.A}{refl}{B}{.B}{refl}{C}{.C}{refl} hrefl hrefl = hrefl
