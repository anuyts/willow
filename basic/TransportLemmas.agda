module willow.basic.TransportLemmas where

open import willow.basic.Identity public
open import willow.basic.Function public

tra-canon : ∀{α β} → {A : Set α} → {a a' : A} → {B : A → Set β} → {p : a == a'} → {b : B a}
  → tra B / p of b == tra idf / map= B p of b
tra-canon {a = a} {.a} {B} {refl} {b} = refl

tra-comp : ∀{α β} → {A : Set α} → {a a' a'' : A} → {B : A → Set β} → {p : a == a'} → {q : a' == a''} → {b : B a}
  → tra B / q of (tra B / p of b) == tra B / (p • q) of b
tra-comp {a = a} {.a} {.a} {B} {refl} {refl} {b} = refl
