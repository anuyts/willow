module aken.basic.Preimage where

open import aken.basic.Function

data _!_↦_ {ℓA ℓB} (A : Set ℓA) {B : Set ℓB} (f : A → B) : B → Set ℓA where
  in! : (a : A) → A ! f ↦ f a --qed

out! : ∀{ℓA ℓB} → {A : Set ℓA} → {B : Set ℓB} → {f : A → B} → {b : B} → (A ! f ↦ b) → A
out! (in! a) = a

mv! : ∀{ℓA ℓB ℓC} → {A : Set ℓA} → {B : Set ℓB} → {C : Set ℓC} → {f : A → B} → (g : B → C) → {b : B} → (A ! f ↦ b) → (A ! (g ∘ f) ↦ g b)
mv! g (in! a) = in! a

map! : ∀{ℓA ℓB ℓC} → {A : Set ℓA} → {B : Set ℓB} → {C : Set ℓC} → (f : A → B) → {g : B → C} → {c : C} → (A ! (g ∘ f) ↦ c) → (B ! g ↦ c)
map! f (in! a) = in! (f a)

Preimage = _!_↦_
syntax Preimage A (λ x → b) b' = [ x ∈ A ! b ≡ b' ]

apply! : ∀{ℓT ℓA ℓB} → {T : Set ℓT} → {A : Set ℓA} → {B : Set ℓB}
  → {g : A → B} → {h : T → B}
  → [ f ∈ (T → A) ! (g ∘ f) ≡ h ] → (t : T) → (A ! g ↦ h t)
apply! (in! f) t = in! (f t)

deduce! : ∀{ℓA ℓB} → {A : Set ℓA} → {B : Set ℓB} → {f : A → B} → {b : B} → (a : A ! f ↦ b) → (f (out! a) == b)
deduce! (in! a) = refl

{-
pull=! : ∀{ℓA ℓB} → {A : Set ℓA} → {B : Set ℓB} → {f : A → B} → {b : B} → (a a' : A ! f ↦ b) → (out! a == out! a') → (a == a')
pull=! (in! a) (in! a') p = {!!}
-}
