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
via _ $ refl • p = p

tra! : ∀{ℓ} {A B : Set ℓ} → (A == B) → (A → B)
tra! refl = λ x → x

map= : ∀ {α β} → {A : Set α} → {B : Set β} → (f : A → B) → {a a' : A} → (p : a == a') → (f a) == (f a')
map= f {a}{.a} refl = refl

transport : ∀{α β} → {A : Set α} → {a a' : A} → (B : A → Set β) → (p : a == a') → (b : B a) → B a'
--transport {α} {β} {A} {a} {.a} B refl b = b
transport B p = tra! (map= B p)
tra_/_of_ = transport
tra_/_ = transport

sym : ∀{α} → {A : Set α} → {a b : A} → (a == b) → (b == a)
sym refl = refl

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance arefl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL arefl #-}

toAgdaEq : ∀{ℓ} {A : Set ℓ} → {a b : A} → (a == b) → a ≡ b
toAgdaEq refl = arefl
