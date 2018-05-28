{-# OPTIONS --type-in-type #-}

open import willow2.cat.Category public
open import willow2.cat.HomFunctor public
open import willow2.cat.FullyFaithfulSubcategory public
open import willow2.cat.Exponential public

module willow2.cat.Lazy where

--cA as a fully faithful subcategory of its presheaf category, enjoys better equational properties.
cLazy : (cA : Cat) → Cat
cLazy cA = cFFSub (cExp (cOp cA) (cSet _)) (λ (x : Obj cA) → c-hom cA c∘ (c-id c, c-const⟨ cOp cA ⟩⟨ cA ⟩ x))

c-toLazy : (cA : Cat) → (cA c→ cLazy cA)
obj (c-toLazy cA) x = x
hom (c-toLazy cA) φ = ffSubHom {!!}
hom-id (c-toLazy cA) = {!!}
hom-comp (c-toLazy cA) = {!!}

c-fromLazy : (cA : Cat) → (cLazy cA c→ cA)
c-fromLazy cA = {!!}

{-
module IsCat {ℓo ℓh} {ObjA : Set ℓo} {HomA : ObjA → ObjA → Set ℓh} {{isCat : IsCat HomA}} where
  cA = cat HomA

  id- : {x : Obj cA} → Hom- cA x x
  id- = nt-id

  _∘-_ : 

  {-
  postulate
    id- : {x : Obj cA} → Hom* cA x x
    _∘-_ : ∀{x y z} → Hom* cA y z → Hom* cA x y → Hom* cA x z
    ⌜_⌝ : ∀{x y} → Hom cA x y → Hom* cA x y
    assoc* : ∀{w x y z : Obj cA} → (ψ : Hom* cA y z) → (ξ : Hom* cA x y) → (φ : Hom* cA w x)
      → (ψ * ξ) * φ ≡ ψ * (ξ * φ)
    lunit* : {x y : Obj cA} → (φ : Hom* cA x y) → id* * φ ≡ φ
    runit* : {x y : Obj cA} → (φ : Hom* cA x y) → φ * id* ≡ φ
    quote-id : ∀{x} → ⌜ id⟨ x ⟩ ⌝ ≡ id*
    quote-comp : ∀{x y z} → {ψ : Hom cA y z} → {φ : Hom cA x y} → ⌜ ψ ∘ φ ⌝ ≡ ⌜ ψ ⌝ * ⌜ φ ⌝
  id*⟨_⟩ : (x : Obj cA) → Hom* cA x x
  id*⟨ x ⟩ = id*

  {-# REWRITE assoc* lunit* runit* #-}

  postulate
    digest : {x y : Obj cA} → Hom* cA x y → Hom cA x y
    digest-id : ∀{x} → digest id* ≡ id⟨ x ⟩
    digest-comp : ∀{x y z} → {ψ : Hom* cA y z} → {φ : Hom* cA x y} → digest (ψ * φ) ≡ digest ψ ∘ digest φ
    digest-quote : ∀{x y} → {φ : Hom cA x y} → digest ⌜ φ ⌝ ≡ φ
    quote-digest : ∀{x y} → (φ : Hom* cA x y) → ⌜ digest φ ⌝ ≡ φ

  {-# REWRITE digest-id digest-comp digest-quote #-}
  -}
open IsCat- public
-}
