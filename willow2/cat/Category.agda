module willow2.cat.Category where

open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Product

open ≡-Reasoning

{-
Graph : ∀ (ℓnA ℓeA : Level) → Set (suc (ℓnA ⊔ ℓeA))
Graph ℓnA ℓeA = Σ[ A ∈ Set ℓnA ] (A → A → Set ℓeA)

record IsCat {ℓoA ℓhA} ()
  -}

record IsCat {ℓoA ℓhA} {A : Set ℓoA} (Hom : A → A → Set ℓhA) : Set (ℓoA ⊔ ℓhA) where
  constructor mkCat
  field
    id-at : (x : A) → Hom x x
    _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

  id : ∀{x} → Hom x x
  id {x} = id-at x

  field
    .assoc : ∀{w x y z : A} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x}
      → (ψ ∘ ξ) ∘ φ ≡ ψ ∘ (ξ ∘ φ)
    .lunit : {x y : A} → {φ : Hom x y} → id ∘ φ ≡ φ
    .runit : {x y : A} → {φ : Hom x y} → φ ∘ id ≡ φ

open IsCat {{...}}

record IsFtr {ℓoA ℓhA ℓoB ℓhB} {A : Set ℓoA} {HomA : A → A → Set ℓhA} {B : Set ℓoB} {HomB : B → B → Set ℓhB}
  {{catA : IsCat HomA}} {{catB : IsCat HomB}} {f : A → B} (homf : ∀{x y} → HomA x y → HomB (f x) (f y))
  : Set (ℓoA ⊔ ℓhA ⊔ ℓoB ⊔ ℓhB) where
  constructor mkFtr
  field
    .hom-id : ∀{x} → homf (id-at x) ≡ id
    .hom-comp : ∀{x y z} {ψ : HomA y z} {φ : HomA x y} → homf (ψ ∘ φ) ≡ homf ψ ∘ homf φ

--_c∘_ : 

{-
record IsCat {ℓA} (A : Set ℓA) (ℓhA : Level) : Set (suc ℓhA ⊔ ℓA) where
  constructor mkCat
  field
    Hom : (x : A) → (y : A) → Set ℓhA
    id : (x : A) → Hom x x
    _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z
    .∘-assoc : {w x y z : A} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x}
      → (ψ ∘ ξ) ∘ φ ≡ ψ ∘ (ξ ∘ φ)
    .∘-lunit : {x y : A} → {φ : Hom x y} → id y ∘ φ ≡ φ
    .∘-runit : {x y : A} → {φ : Hom x y} → φ ∘ id x ≡ φ

open IsCat {{...}}

record IsFtr {ℓA ℓhA ℓB ℓhB} {A : Set ℓA} {B : Set ℓB} {{catA : IsCat A ℓhA}} {{catB : IsCat B ℓhB}} (f : A → B) : Set {!!} where
  constructor mkFtr
  field
    hom : ∀{x y} → Hom x y → Hom (f x) (f y)
    .hom-id : ∀{x : A} → hom (id x) ≡ id (f x)
    .hom-∘ : ∀{x y z} {ψ : Hom y z} {φ : Hom x y} → hom (ψ ∘ φ) ≡ hom ψ ∘ hom φ
-}

{-
record Cat (α β : Level) : Set (suc (α ⊔ β)) where
  --no-eta-equality
  constructor mkCat
  field
    Obj : Set α
    {{Hom}} : (x : Obj) → (y : Obj) → Set β
    {{id}} : {x : Obj} → Hom x x
    {{comp}} : {x y z : Obj} → (ψ : Hom y z) → (φ : Hom x y) → Hom x z
    .{{comp-assoc}} : {w x y z : Obj} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x}
      → comp (comp ψ ξ) φ ≡ comp ψ (comp ξ φ)
    .{{comp-lunit}} : {x y : Obj} → {φ : Hom x y} → comp id φ ≡ φ
    .{{comp-runit}} : {x y : Obj} → {φ : Hom x y} → comp φ id ≡ φ

  id⟨_⟩ = id
  syntax comp c ψ φ = ψ ∘⟨ c ⟩ φ

open Cat
--module c = Cat

record Ftr {ℓoA ℓhA ℓoB ℓhB} (cA : Cat ℓoA ℓhA) (cB : Cat ℓoB ℓhB) : Set (ℓoA ⊔ ℓhA ⊔ ℓoB ⊔ ℓhB) where
  --no-eta-equality
  constructor mkFtr
  field
    obj : Obj cA → Obj cB
    hom : ∀{x y} → Hom cA x y → Hom cB (obj x) (obj y)
    .hom-id : ∀{x} → hom (id⟨ cA ⟩ {x}) ≡ id⟨ cB ⟩
    .hom-comp : ∀{x y z} {ψ : Hom cA y z} {φ : Hom cA x y} → hom (ψ ∘⟨ cA ⟩ φ) ≡ hom ψ ∘⟨ cB ⟩ hom φ

open Ftr

_c→_ = Ftr
infix 1 _c→_

_c∘_ : ∀{ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {cC : Cat ℓoC ℓhC}
  → (cB c→ cC) → (cA c→ cB) → (cA c→ cC)
obj (cg c∘ cf) x = obj cg (obj cf x)
hom (cg c∘ cf) φ = hom cg (hom cf φ)
hom-id (cg c∘ cf) = hom cg (hom cf id⟨ _ ⟩) ≡⟨ cong (hom cg) (hom-id cf) ⟩ hom cg id⟨ _ ⟩ ≡⟨ hom-id cg ⟩ id⟨ _ ⟩ ∎
hom-comp (cg c∘ cf) = {!!}
-}
