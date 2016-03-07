module aken.basic.QEquivalence where

open import aken.basic.Function

record _≈_ {α β}  (A : Set α) (B : Set β) : Set (lsuc (α ⊔ β)) where
  constructor prove≈
  field
    ≈fwd : A → B
    ≈bck : B → A
    ≈fwdAndBck : ≈bck ∘ ≈fwd == id
    ≈bckAndFwd : ≈fwd ∘ ≈bck == id
open _≈_ public

  --prove≈ : {A : Set α} -> {B : Set β} -> (f : A -> B) -> (g : B -> A) -> ((g ∘ f) == id) -> (f ∘ g == id{β}{B}) -> A ≈ B

≈sym : {α β : Level} -> {A : Set α} -> {B : Set β} -> (A ≈ B) -> (B ≈ A)
≈sym (prove≈ f g p q) = prove≈ g f q p

≈trans : {α β γ : Level} -> {A : Set α} -> {B : Set β} -> {C : Set γ} -> (A ≈ B) -> (B ≈ C) -> (A ≈ C)
≈trans (prove≈ f g p q) (prove≈ f' g' p' q') = prove≈ (f' ∘ f) (g ∘ g')
  (
    via ((g ∘ g') ∘ (f' ∘ f)) $ refl • 
    via (((g ∘ g') ∘ f') ∘ f) $ (∘assoc f f' (g ∘ g')) • 
    via ((g ∘ (g' ∘ f')) ∘ f) $ (map= (λ φ -> φ ∘ f) (∘assoc f' g' g)) •
    via ((g ∘ id) ∘ f) $ (map= (λ φ -> (g ∘ φ) ∘ f) p') •
    via (g ∘ f) $ (map= (λ φ -> φ ∘ f) (∘rightUnity g)) •
    p
  )
  (
    via (f' ∘ f) ∘ (g ∘ g') $ refl •
    via (((f' ∘ f) ∘ g) ∘ g') $ (∘assoc g' g (f' ∘ f)) •
    via ((f' ∘ (f ∘ g)) ∘ g') $ (map= (λ φ -> φ ∘ g') (∘assoc g f f')) •
    via ((f' ∘ id) ∘ g') $ (map= (λ φ -> (f' ∘ φ) ∘ g') q) •
    via (f' ∘ g') $ (map= (λ φ -> φ ∘ g') (∘rightUnity f')) •
    q'
  )

≈refl : {α : Level} -> {A : Set α} -> (A ≈ A)
≈refl = prove≈ id id refl refl

{-
≈fwd : {α β : Level} -> {A : Set α} -> {B : Set β} -> (A ≈ B) -> A -> B
≈fwd (prove≈ f g p q) = f

≈bck : {α β : Level} -> {A : Set α} -> {B : Set β} -> (A ≈ B) -> B -> A
≈bck (prove≈ f g p q) = g

≈fwdAndBck : {α β : Level} -> {A : Set α} -> {B : Set β} -> (equiv : A ≈ B) -> (≈bck equiv) ∘ (≈fwd equiv) == id
≈fwdAndBck (prove≈ f g p q) = p

≈bckAndFwd : {α β : Level} -> {A : Set α} -> {B : Set β} -> (equiv : A ≈ B) -> (≈fwd equiv) ∘ (≈bck equiv) == id
≈bckAndFwd (prove≈ f g p q) = q
-}
