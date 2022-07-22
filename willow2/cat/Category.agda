{-# OPTIONS --type-in-type --rewriting --irrelevant-projections #-}

{- INTENDED IMPROVEMENTS OF willow2 OVER willow:

  * Use of the standard library
  * Use of instance arguments (but are they useful here?)
    * For structure on types: yes
    * For structure on functions: less so
  * Use of irrelevance
  * Level in the record

-}

module willow2.cat.Category where

open import willow2.basic.PropositionalEquality public
open import willow2.basic.HeterogeneousEquality public
open import Level public
open import Data.Product
open import Function renaming (_∘_ to _f∘_ ; id to f-id) public
open import willow2.basic.Funext public
open import willow2.basic.Superbasic public


Setω = Set
ℓ? : Level
ℓ? = zero

record IsCat {ℓo ℓh} {Obj : Set ℓo} (Hom : Obj → Obj → Set ℓh) : Set (ℓo ⊔ ℓh) where
  field
    id⟨_⟩ : (x : Obj) → Hom x x
    _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z
  infix 10 _∘_

  id : ∀{x} → Hom x x
  id {x} = id⟨ x ⟩

  field
    .assoc : ∀{w x y z : Obj} → (ψ : Hom y z) → (ξ : Hom x y) → (φ : Hom w x)
      → (ψ ∘ ξ) ∘ φ ≡ ψ ∘ (ξ ∘ φ)
    .lunit : {x y : Obj} → (φ : Hom x y) → id ∘ φ ≡ φ
    .runit : {x y : Obj} → (φ : Hom x y) → φ ∘ id ≡ φ
open IsCat {{...}} public

{-# DISPLAY IsCat.id⟨_⟩ _ _ = id #-}
{-# DISPLAY IsCat._∘_ _ ψ φ = ψ ∘ φ #-}

record Cat : Setω where
  constructor cat
  field
    {ℓo ℓh} : Level
    {Obj} : Set ℓo
    Hom : (x y : Obj) → Set ℓh
    {{isCat}} : IsCat Hom

  postulate
    Hom* : (x y : Obj) → Set ℓh
    --MotHom* : ∀{ℓ} → (T : ∀{x y : Obj} (φs : Hom* x y) → Set ℓ) → Set ℓ
open Cat public

--module IsCat* {cA : Cat} where
module IsCat* {ℓo ℓh} {ObjA : Set ℓo} {HomA : ObjA → ObjA → Set ℓh} {{isCat : IsCat HomA}} where
  cA = cat HomA
  postulate
    id* : {x : Obj cA} → Hom* cA x x
    _*_ : ∀{x y z} → Hom* cA y z → Hom* cA x y → Hom* cA x z
    ⌜_⌝ : ∀{x y} → Hom cA x y → Hom* cA x y
    assoc* : ∀{w x y z : Obj cA} → (ψ : Hom* cA y z) → (ξ : Hom* cA x y) → (φ : Hom* cA w x)
      → (ψ * ξ) * φ ≡ ψ * (ξ * φ)
    lunit* : {x y : Obj cA} → (φ : Hom* cA x y) → id* * φ ≡ φ
    runit* : {x y : Obj cA} → (φ : Hom* cA x y) → φ * id* ≡ φ
    quote-id : ∀{x : ObjA} → ⌜ id⟨ x ⟩ ⌝ ≡ id*
    quote-comp : ∀{x y z} → {ψ : Hom cA y z} → {φ : Hom cA x y} → ⌜ ψ ∘ φ ⌝ ≡ ⌜ ψ ⌝ * ⌜ φ ⌝
  id*⟨_⟩ : (x : Obj cA) → Hom* cA x x
  id*⟨ x ⟩ = id*

  {-# REWRITE assoc* lunit* runit* #-}

  postulate
    digest : {x y : Obj cA} → Hom* cA x y → Hom cA x y
    digest-id : ∀{x : ObjA} → digest id* ≡ id⟨ x ⟩
    digest-comp : ∀{x y z} → {ψ : Hom* cA y z} → {φ : Hom* cA x y} → digest (ψ * φ) ≡ digest ψ ∘ digest φ
    digest-quote : ∀{x y} → {φ : Hom cA x y} → digest ⌜ φ ⌝ ≡ φ
    quote-digest : ∀{x y} → (φ : Hom* cA x y) → ⌜ digest φ ⌝ ≡ φ

  {-# REWRITE digest-id digest-comp digest-quote #-}
open IsCat* hiding (cA) public

record Ftr (cA cB : Cat) : Set (ℓo cA ⊔ ℓh cA ⊔ ℓo cB ⊔ ℓh cB) where
  constructor ftr
  field
    {obj} : (x : Obj cA) → Obj cB
    hom : ∀{x y} → (φ : Hom cA x y) → Hom cB (obj x) (obj y)
    --{{isFtr}} : IsFtr cA cB hom
    .{{hom-id}} : ∀{x : Obj cA} → hom (id⟨ x ⟩) ≡ id
    .{{hom-comp}} : ∀{x y z} {ψ : Hom cA y z} {φ : Hom cA x y} → hom (ψ ∘ φ) ≡ hom ψ ∘ hom φ

  postulate
    --hom* is a definable function on the QIT
    hom* : ∀{x y} → (φ : Hom* cA x y) → Hom* cB (obj x) (obj y)
    hom*-id : ∀{x} → hom* (id*⟨ x ⟩) ≡ id*
    hom*-comp : ∀{x y z} (ψ : Hom* cA y z) (φ : Hom* cA x y) → hom* (ψ * φ) ≡ hom* ψ * hom* φ
    hom*-quote : ∀{x y} {φ : Hom cA x y} → hom* ⌜ φ ⌝ ≡ ⌜ hom φ ⌝
    --digest-hom* and hom*-quote together break confluence, since hom digest ψ ∘ hom digest φ ≠ hom (digest ψ ∘ digest φ)
  {-# REWRITE hom*-id hom*-comp hom*-quote #-}

  postulate
    --hom⌜_⌝ is a constructor (with computation) of the QIT
    hom⌜_⌝ : ∀{x y} → (φ : Hom* cA x y) → Hom* cB (obj x) (obj y)
    hom⌜_⌝-id : ∀{x} → hom⌜_⌝ (id*⟨ x ⟩) ≡ id*
    hom⌜_⌝-comp : ∀{x y z} (ψ : Hom* cA y z) (φ : Hom* cA x y) → hom⌜_⌝ (ψ * φ) ≡ hom⌜_⌝ ψ * hom⌜_⌝ φ
    digest-hom⌜_⌝ : ∀{x y} {φ : Hom* cA x y} → digest (hom⌜_⌝ φ) ≡ hom (digest φ)
  {-# REWRITE hom⌜_⌝-id hom⌜_⌝-comp digest-hom⌜_⌝ #-}

  hom⌜_⌝=hom* : ∀{x y} (φ : Hom* cA x y) → hom⌜_⌝ φ ≡ hom* φ
  hom⌜_⌝=hom* {x}{y} φ = begin
    hom⌜_⌝ φ
      ≡⟨ sym (quote-digest _) ⟩
    ⌜ digest (hom⌜_⌝ φ) ⌝
      ≡⟨ refl ⟩
    ⌜ hom (digest φ) ⌝
      ≡⟨ refl ⟩
    hom* ⌜ digest φ ⌝
      ≡⟨ cong hom* (quote-digest φ) ⟩
    hom* φ ∎
    
  digest-hom* : ∀{x y} (φ : Hom* cA x y) → digest (hom* φ) ≡ hom (digest φ)
  digest-hom* {x}{y} φ = cong digest (sym (hom⌜_⌝=hom* φ))

  hom⌜_⌝-quote : ∀{x y} (φ : Hom cA x y) → hom⌜_⌝ ⌜ φ ⌝ ≡ ⌜ hom φ ⌝
  hom⌜_⌝-quote {x}{y} φ = hom⌜_⌝=hom* ⌜ φ ⌝
open Ftr public
_c→_ = Ftr
infix 1 _c→_

c-id : ∀{cA} → (cA c→ cA)
c-id = ftr f-id

c-id⟨_⟩ : (cA : Cat) → (cA c→ cA)
c-id⟨ cA ⟩ = c-id

_c∘_ : ∀ {cA cB cC : Cat} → (cB c→ cC) → (cA c→ cB) → (cA c→ cC)
obj (cg c∘ cf) = obj cg f∘ obj cf
hom (cg c∘ cf) = hom cg f∘ hom cf
hom-id (cg c∘ cf) = begin
          hom cg (hom cf id)
            ≡⟨ cong (hom cg) (hom-id cf) ⟩
          hom cg id
            ≡⟨ hom-id cg ⟩
          id ∎
hom-comp (cg c∘ cf) {ψ = ψ} {φ} = begin
          hom cg (hom cf (ψ ∘ φ))
            ≡⟨ cong (hom cg) (hom-comp cf {ψ = ψ} {φ}) ⟩
          hom cg (hom cf ψ ∘ hom cf φ)
            ≡⟨ hom-comp cg {ψ = hom cf ψ} {hom cf φ} ⟩
          hom cg (hom cf ψ) ∘ hom cg (hom cf φ) ∎

c-const : ∀{cA cB} → Obj cB → (cA c→ cB)
obj (c-const b) x = b
hom (c-const b) φ = id
hom-id (c-const b) = refl
hom-comp (c-const b) = sym (lunit id⟨ b ⟩)

c-const⟨_⟩⟨_⟩ : (cA cB : Cat) → Obj cB → (cA c→ cB)
c-const⟨ _ ⟩⟨ _ ⟩ = c-const

{-
record IsNT {cA cB : Cat} (cf cg : cA c→ cB) (ν : (a : Obj cA) → Hom cB (obj cf a) (obj cg a)) : Set ℓ? where
  instance
    constructor pvNT
  field
    .nat : ∀{x y} → (φ : Hom cA x y) → hom cg φ ∘ ν x ≡ ν y ∘ hom cf φ
open IsNT
-}

record NT {cA cB : Cat} (cf cg : cA c→ cB) : Set ℓ? where
  constructor nt
  field
    obj : (a : Obj cA) → Hom cB (obj cf a) (obj cg a)
    --{{isNT}} : IsNT cf cg obj
    .{{nat}} : ∀{x y} → {φ : Hom cA x y} → hom cg φ ∘ obj x ≡ obj y ∘ hom cf φ
open NT public
_nt→_ = NT
infix 1 _nt→_

ext-nt : ∀{cA cB : Cat} {cf cg : cA c→ cB} {nta ntb : cf nt→ cg} → (obj nta ≡ obj ntb) → nta ≡ ntb
ext-nt {cA} {cB} {cf} {cg} {nt .(obj ntb)} {ntb} refl = refl

nt-id : ∀{cA cB} {cf : cA c→ cB} → (cf nt→ cf)
obj (nt-id {cA} {cB} {cf}) a = id
nat (nt-id {cA} {cB} {cf}) {x}{y} {φ} = begin
          hom cf φ ∘ id⟨ obj cf x ⟩
            ≡⟨ runit _ ⟩
          hom cf φ
            ≡⟨ sym (lunit _) ⟩
          id⟨ obj cf y ⟩ ∘ hom cf φ ∎

nt-id⟨_⟩ : ∀{cA cB} (cf : cA c→ cB) → (cf nt→ cf)
nt-id⟨ _ ⟩ = nt-id

_nt∘_ : ∀{cA cB} {cf cg ch : cA c→ cB} (ntb : cg nt→ ch) (nta : cf nt→ cg) → (cf nt→ ch)
obj (_nt∘_ {cA} {cB} {cf} {cg} {ch} ntb nta) a = obj ntb a ∘ obj nta a
nat (_nt∘_ {cA} {cB} {cf} {cg} {ch} ntb nta) {x}{y} {φ} = begin
          hom ch φ ∘ (obj ntb x ∘ obj nta x)
            ≡⟨ sym (assoc _ _ _) ⟩
          (hom ch φ ∘ obj ntb x) ∘ obj nta x
            ≡⟨ cong (λ ψ → ψ ∘ (obj nta x)) (nat ntb) ⟩
          (obj ntb y ∘ hom cg φ) ∘ obj nta x
            ≡⟨ assoc _ _ _ ⟩
          obj ntb y ∘ (hom cg φ ∘ obj nta x)
            ≡⟨ cong (λ ψ → obj ntb y ∘ ψ) (nat nta) ⟩
          obj ntb y ∘ (obj nta y ∘ hom cf φ)
            ≡⟨ sym (assoc _ _ _) ⟩
          (obj ntb y ∘ obj nta y) ∘ hom cf φ ∎

_nt⊚_ : ∀{cA cB cC} {cf cg : cA c→ cB} {ch ck : cB c→ cC} (ntb : ch nt→ ck) (nta : cf nt→ cg) → (ch c∘ cf nt→ ck c∘ cg)
obj (_nt⊚_ {cA} {cB} {cC} {cf} {cg} {ch} {ck} ntb nta) a =
  {-  h f a  →[h nta a]→  h g a  →[ntb g a]→  k g a  -}
  obj ntb (obj cg a) ∘ hom ch (obj nta a)
nat (_nt⊚_ {cA} {cB} {cC} {cf} {cg} {ch} {ck} ntb nta) {a}{b} {φ} = begin
  {-  h f a  →[h nta a]→  h g a  →[ntb g a]→  k g a  -}
  {-    ↓                     ↓                     ↓     -}
  {- [h f φ]               [h g φ]               [k g φ] -}
  {-    ↓                     ↓                     ↓     -}
  {-  h f b  →[h nta b]→  h g b  →[ntb g b]→  k g b  -}
  hom ck (hom cg φ) ∘ (obj ntb (obj cg a) ∘ hom ch (obj nta a))
    ≡⟨ sym (assoc _ _ _) ⟩
  (hom ck (hom cg φ) ∘ obj ntb (obj cg a)) ∘ hom ch (obj nta a)
    ≡⟨ cong (λ ψ → ψ ∘ _) (nat ntb {φ = hom cg φ}) ⟩
  (obj ntb (obj cg b) ∘ hom ch (hom cg φ)) ∘ hom ch (obj nta a)
    ≡⟨ assoc _ _ _ ⟩
  obj ntb (obj cg b) ∘ (hom ch (hom cg φ) ∘ hom ch (obj nta a))
    ≡⟨ cong (λ ψ → _ ∘ ψ) (begin
       hom ch (hom cg φ) ∘ hom ch (obj nta a)
         ≡⟨ sym (hom-comp ch) ⟩
       hom ch (hom cg φ ∘ obj nta a)
         ≡⟨ cong (hom ch) (nat nta {φ = φ}) ⟩
       hom ch (obj nta b ∘ hom cf φ)
         ≡⟨ hom-comp ch ⟩
       hom ch (obj nta b) ∘ hom ch (hom cf φ)
         ∎) ⟩
  obj ntb (obj cg b) ∘ (hom ch (obj nta b) ∘ hom ch (hom cf φ))
    ≡⟨ sym (assoc _ _ _) ⟩
  (obj ntb (obj cg b) ∘ hom ch (obj nta b)) ∘ hom ch (hom cf φ) ∎
