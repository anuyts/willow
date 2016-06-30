module willow.basic.UIP where

open import willow.basic.Basic public
open import willow.basic.Propositional public

uip : ∀{α} → {A : Set α} → {a b : A} → Is¶ (a == b)
uip {ℓ}{A}{a}{.a}{refl}{refl}= refl

primitive
  primTrustMe : {a : Level} {A : Set a} {x y : A} → x ≡ y
  
private
  trustMe : ∀{ℓ} {A : Set ℓ} {x y : A} → x == y
  trustMe = from≡ primTrustMe

trust : ∀{ℓ} {A : Set ℓ} {x y : A} → x == y → x == y
trust p = trustMe
