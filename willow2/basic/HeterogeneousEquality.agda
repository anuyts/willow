module willow2.basic.HeterogeneousEquality where

open import willow2.basic.PropositionalEquality public
open import Relation.Binary.HeterogeneousEquality as ≅
  renaming (cong to hcong ; sym to hsym ; trans to htrans ; cong-app to hcong-app ; cong₂ to hcong₂)
  using (_≅_ ; refl ; ≡-to-≅ ; ≅-to-≡) public

open ≅.≅-Reasoning renaming (begin_ to hbegin_ ; _∎ to _h∎) using (_≅⟨_⟩_) public

[_∋_]≅[_∋_] : ∀{ℓ} (A : Set ℓ) → A → (B : Set ℓ) → B → Set ℓ
[ A ∋ a ]≅[ B ∋ b ] = a ≅ b
{-# DISPLAY _≅_ {_} {A} a {B} b = [ A ∋ a ]≅[ B ∋ b ] #-}

postulate
  instance ≅choice : ∀{ℓ}{A B : Set ℓ}{a : A}{b : B} → Choice (a ≅ b)

postulate
  injΠ-cod : ∀{ℓA ℓB} {A A' : Set ℓA} {B : A → Set ℓB} {B' : A' → Set ℓB}
    → ((x : A) → B x) ≡ ((x' : A') → B' x') → B ≅ B'

hrefl⟨_⟩ : ∀{ℓ} {A : Set ℓ} → (a : A) → a ≅ a
hrefl⟨ _ ⟩ = refl

≅-to-type : ∀{ℓ} {A A' : Set ℓ} {a : A} {a' : A'} → a ≅ a' → A ≡ A'
≅-to-type refl = refl

hap : ∀{ℓA ℓB} {A A' : Set ℓA} {B : A → Set ℓB} {B' : A' → Set ℓB}
           {f : (x : A) → B x} {f' : (x' : A') → B' x'}
           {a : A} {a' : A'}
           → (f ≅ f') → (a ≅ a') → (f a ≅ f' a')
hap f= refl with injΠ-cod (≅-to-type f=)
hap refl refl | refl = refl

_-hap-_ = hap

{-
hap-irr : ∀{ℓA ℓB} {A A' : Set ℓA} {B : A → Set ℓB} {B' : A' → Set ℓB}
           {f : .(x : A) → B x} {f' : .(x' : A') → B' x'}
           {a : A} {a' : A'}
           → (f ≅ f') → (B ≅ B') → (f a ≅ f' a')
-}

!>≅ : ∀{ℓ} {A B : Set ℓ} {a : A} .{e : A ≡ B} → a !> e ≅ a
!>≅ {ℓ}{A}{B}{a}{e} with choose e
!>≅ {ℓ} {A} {.A} {a} {e} | refl = refl

!>≅!> : ∀{ℓ} {A B C : Set ℓ} {a : A} .{e : A ≡ B} .{e' : A ≡ C} → a !> e ≅ a !> e'
!>≅!> {ℓ}{A}{B}{C}{a}{e}{e'} with choose e | choose e'
!>≅!> {ℓ}{A}{.A}{.A}{a}{e}{e'} | refl | refl = refl

open import Data.Product
!>× : ∀{ℓ} {A B A' B' : Set ℓ} {a : A} {b : B} .{eA : A ≡ A'} .{eB : B ≡ B'} .{e : (A × B) ≡ (A' × B')}
  → ((a !> eA) , (b !> eB)) ≡ ((a , b) !> e)
!>× {ℓ}{A}{B}{A'}{B'}{a}{b}{eA}{eB}{e} with choose eA | choose eB | choose e
... | refl | refl | refl = refl

hext-× : ∀{ℓA ℓB} {A A' : Set ℓA} {B B' : Set ℓB} {p : A × B} {q : A' × B'} → proj₁ p ≅ proj₁ q → proj₂ p ≅ proj₂ q → p ≅ q
hext-× refl refl = refl

ext-Σ : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {p q : Σ[ a ∈ A ] B a} → proj₁ p ≡ proj₁ q → proj₂ p ≅ proj₂ q → p ≡ q
ext-Σ refl refl = refl

snd-app : ∀{ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {p q : Σ[ a ∈ A ] B a} → p ≡ q → proj₂ p ≅ proj₂ q
snd-app refl = refl
