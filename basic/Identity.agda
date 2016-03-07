module willow.basic.Identity where

open import willow.basic.Levels public

data _$_==_ {α} (A : Set α) : A → A → Set α where
  refl : {a : A} → A $ a == a

_==_ : ∀{α} → {A : Set α} → A → A → Set α
a == b = _ $ a == b

infix 1 _==_

--\bu
--ACHTUNG: I changed order!
_•_ : ∀ {α} → {A : Set α} → {a b c : A} → (a == b) → (b == c) → (a == c)
refl • refl = refl

infixl 10 _•_

via_$_•_ : ∀ {α} → {A : Set α} → {a c : A} → (b : A) → (a == b) → (b == c) → (a == c)
via _ $ refl • refl = refl

transport : ∀{α β} → {A : Set α} → {a a' : A} → (B : A → Set β) → (p : a == a') → (b : B a) → B a'
transport {α} {β} {A} {a} {.a} B refl b = b
tra_/_of_ = transport
tra_/_ = transport

sym : ∀{α} → {A : Set α} → {a b : A} → (a == b) → (b == a)
sym refl = refl
