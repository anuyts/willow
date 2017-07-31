{-# OPTIONS --type-in-type #-}

module willow2.cat.Category where

open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Product
open import Function renaming (_∘_ to _f∘_ ; id to f-id)
open import willow2.basic.Funext
open import willow2.basic.Superbasic

open ≡-Reasoning

Setω = Set

{-
Graph : ∀ (ℓnA ℓeA : Level) → Set (suc (ℓnA ⊔ ℓeA))
Graph ℓnA ℓeA = Σ[ A ∈ Set ℓnA ] (A → A → Set ℓeA)

record IsCat {ℓoA ℓhA} ()
  -}

record IsCat {ℓo ℓh} {Obj : Set ℓo} (Hom : Obj → Obj → Set ℓh) : Set (ℓo ⊔ ℓh) where
  field
    id-at : (x : Obj) → Hom x x
    _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

  id : ∀{x} → Hom x x
  id {x} = id-at x

  field
    .assoc : ∀{w x y z : Obj} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x}
      → (ψ ∘ ξ) ∘ φ ≡ ψ ∘ (ξ ∘ φ)
    .lunit : {x y : Obj} → (φ : Hom x y) → id ∘ φ ≡ φ
    .runit : {x y : Obj} → (φ : Hom x y) → φ ∘ id ≡ φ
open IsCat {{...}}

record Cat : Setω where
  constructor cat
  field
    {ℓo ℓh} : Level
    {Obj} : Set ℓo
    Hom : Obj → Obj → Set ℓh
    {{isCat}} : IsCat Hom
open Cat

record IsFtr
  --{A : Set ℓoA} {HomA : A → A → Set ℓhA} {{catA : IsCat HomA}}
  --{B : Set ℓoB} {HomB : B → B → Set ℓhB} {{catB : IsCat HomB}}
  --{f : A → B} (homf : ∀{x y} → HomA x y → HomB (f x) (f y))
  (cA cB : Cat)
  {f : Obj cA → Obj cB} (homf : ∀{x y} → Hom cA x y → Hom cB (f x) (f y))
  : Set (ℓo cA ⊔ ℓh cA ⊔ ℓo cB ⊔ ℓh cB) where
  instance
    constructor pvFtr
  field
    .hom-id : ∀{x} → homf (id-at x) ≡ id
    .hom-comp : ∀{x y z} (ψ : Hom cA y z) (φ : Hom cA x y) → homf (ψ ∘ φ) ≡ homf ψ ∘ homf φ
open IsFtr {{...}}

record Ftr (cA cB : Cat) : Set (ℓo cA ⊔ ℓh cA ⊔ ℓo cB ⊔ ℓh cB) where
  constructor ftr
  field
    {obj} : Obj cA → Obj cB
    hom : ∀{x y} → Hom cA x y → Hom cB (obj x) (obj y)
    {{isFtr}} : IsFtr cA cB hom
open Ftr
_c→_ = Ftr
infix 1 _c→_

_c∘_ : ∀ {cA cB cC : Cat} → (cB c→ cC) → (cA c→ cB) → (cA c→ cC)
cg c∘ cf = ftr (hom cg f∘ hom cf) {{proof}}
  where proof : IsFtr _ _ _
        IsFtr.hom-id proof {x} = begin
          hom cg (hom cf id)
            ≡⟨ cong (hom cg) hom-id ⟩
          hom cg id
            ≡⟨ hom-id ⟩
          id ∎
        IsFtr.hom-comp proof ψ φ = begin
          hom cg (hom cf (ψ ∘ φ))
            ≡⟨ cong (hom cg) (hom-comp ψ φ) ⟩
          hom cg (hom cf ψ ∘ hom cf φ)
            ≡⟨ hom-comp (hom cf ψ) (hom cf φ) ⟩
          hom cg (hom cf ψ) ∘ hom cg (hom cf φ) ∎

c-id : ∀{cA} → (cA c→ cA)
c-id = ftr f-id

cConst : ∀{cA cB} → Obj cB → (cA c→ cB)
cConst b = ftr (λ φ → id-at b) {{proof}}
  where proof : IsFtr _ _ _
        IsFtr.hom-id proof = refl
        IsFtr.hom-comp proof ψ φ = sym (lunit id)

