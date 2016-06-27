module willow.basic.Propositional.HeteroIdentity where

open import willow.basic.Propositional
open import willow.basic.Identity
open import willow.basic.Sum
open import willow.basic.Function

data _,_$_===_ {ℓ} : (A B : Set ℓ) → (a : A) → (b : B) → Set ℓ where
  hrefl : {A : Set ℓ} → {a : A} → A , A $ a === a

_===_ : ∀{ℓ} → {A B : Set ℓ} → A → B → Set ℓ
a === b = _ , _ $ a === b

infix 1 _===_

pathunder : ∀{ℓ} → {A B : Set ℓ} → {a : A} → {b : B} → (a === b) → (A == B)
pathunder hrefl = refl

postulate dom-inj : ∀{ℓA ℓB} {A A' : Set ℓA} → {B : A → Set ℓB} {B' : A' → Set ℓB} → ((a : A) → B a) == ((a : A') → B' a) → A == A'
postulate codom-inj : ∀{ℓA ℓB} {A A' : Set ℓA} → {B : A → Set ℓB} {B' : A' → Set ℓB} → ((a : A) → B a) == ((a : A') → B' a) → B === B'
postulate domi-inj : ∀{ℓA ℓB} {A A' : Set ℓA} → {B : A → Set ℓB} {B' : A' → Set ℓB} → ({a : A} → B a) == ({a : A'} → B' a) → A == A'
postulate codomi-inj : ∀{ℓA ℓB} {A A' : Set ℓA} → {B : A → Set ℓB} {B' : A' → Set ℓB} → ({a : A} → B a) == ({a : A'} → B' a) → B === B'

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

htra! : ∀{ℓ} {A B : Set ℓ} → (p : A == B) → (tra! p === idf {X = A})
htra! refl = hrefl

pair-hext : ∀{α β} → {A : Set α} → {B : A → Set β}
  → {a a' : A} → (p : a == a')
  → {b : B a} → {b' : B a'} → (q : b === b')
  → (a , b) == (a' , b')
pair-hext {_}{_} {A}{B} {a}{.a} refl {b}{.b} hrefl = refl

{-
comp-hlemma : ∀{ℓA ℓB ℓC} → {A A' : Set ℓA} (R : A == A') → {B B' : Set ℓB} (S : B == B') → {C C' : Set ℓC} (T : C == C')
  → {f : A → B} → {f' : A' → B'} → (p : f === f')
  → {g : B → C} → {g' : B' → C'} → (q : g === g')
  → (g ∘ f === g' ∘ f')
comp-hlemma {A = A}{.A} refl {B}{.B} refl {C}{.C} refl hrefl hrefl = hrefl
-}

hhapply : ∀{ℓA ℓB} → {A : Set ℓA} → {B B' : A → Set ℓB} → {f : (a : A) → B a} {g : (a : A) → B' a }
  → f === g → ((a : A) → (f a === g a))
hhapply p with codom-inj (pathunder p)
hhapply hrefl | hrefl = λ a → hrefl
--hhapply hrefl = λ a → hrefl

hdmap= : ∀ {ℓA ℓB} → {A : Set ℓA} → {B : A → Set ℓB} → (f : (a : A) → B a) → {a a' : A} → (p : a == a') → (f a) === (f a')
hdmap= f {a}{.a} refl = hrefl

hdmapi= : ∀ {ℓA ℓB} → {A : Set ℓA} → {B : A → Set ℓB} → (f : {a : A} → B a) → {a a' : A} → (p : a == a') → (f {a}) === (f {a'})
hdmapi= f {a}{.a} refl = hrefl

aph= : ∀ {ℓA ℓB} → {A A' : Set ℓA} → {B : A → Set ℓB} {B' : A' → Set ℓB} → {f : (a : A) → B a} {f' : (a' : A') → B' a'}
  → (=f : f === f') → {a : A} {a' : A'} → (=a : a === a') → (f a === f' a')
aph= =f =a with codom-inj (pathunder =f)
aph= hrefl hrefl | hrefl = hrefl

_=aph=_ = aph=
infixl 1 _=aph=_

aphi= : ∀ {ℓA ℓB} → {A A' : Set ℓA} → {B : A → Set ℓB} {B' : A' → Set ℓB} → {f : {a : A} → B a} {f' : {a' : A'} → B' a'}
  → (=f : ({a : A} → B a) , ({a' : A'} → B' a') $ f === f') → {a : A} {a' : A'} → (=a : a === a') → (f {a} === f' {a'})
aphi= =f =a with codomi-inj (pathunder =f)
aphi= hrefl hrefl | hrefl = hrefl

_=aphi=_ = aphi=
infixl 1 _=aphi=_

--this should be provable!
uhip : ∀{ℓ} {A B : Set ℓ} {a : A} {b : B} {p q : a === b} → p == q
uhip {p = hrefl}{hrefl} = refl
huip : ∀{ℓ} {A B : Set ℓ} {a a' : A} {b b' : B} {p : a == a'} {q : b == b'} → (a === b) → p === q
huip {p = refl}{refl} hrefl = hrefl
