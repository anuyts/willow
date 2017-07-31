{-# OPTIONS --type-in-type #-}

{- INTENDED IMPROVEMENTS OF willow2 OVER willow:

  * Use of the standard library
  * Use of instance arguments (but are they useful here?)
    * For structure on types: yes
    * For structure on functions: less so
  * Use of irrelevance
  * Level in the record

-}

module willow2.cat.Category where

open import Relation.Binary.PropositionalEquality public
open import Level public
open import Data.Product
open import Function renaming (_∘_ to _f∘_ ; id to f-id) public
open import willow2.basic.Funext public
open import willow2.basic.Superbasic public

open ≡-Reasoning public

Setω = Set
ℓ? : Level
ℓ? = zero

{-
Graph : ∀ (ℓnA ℓeA : Level) → Set (suc (ℓnA ⊔ ℓeA))
Graph ℓnA ℓeA = Σ[ A ∈ Set ℓnA ] (A → A → Set ℓeA)

record IsCat {ℓoA ℓhA} ()
  -}

record IsCat {ℓo ℓh} {Obj : Set ℓo} (Hom : Obj → Obj → Set ℓh) : Set (ℓo ⊔ ℓh) where
  field
    id⟨_⟩ : (x : Obj) → Hom x x
    _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

  id : ∀{x} → Hom x x
  id {x} = id⟨ x ⟩

  field
    .assoc : ∀{w x y z : Obj} → (ψ : Hom y z) → (ξ : Hom x y) → (φ : Hom w x)
      → (ψ ∘ ξ) ∘ φ ≡ ψ ∘ (ξ ∘ φ)
    .lunit : {x y : Obj} → (φ : Hom x y) → id ∘ φ ≡ φ
    .runit : {x y : Obj} → (φ : Hom x y) → φ ∘ id ≡ φ
open IsCat {{...}} public

record Cat : Setω where
  constructor cat
  field
    {ℓo ℓh} : Level
    {Obj} : Set ℓo
    Hom : (x y : Obj) → Set ℓh
    {{isCat}} : IsCat Hom
open Cat public

{-
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
-}

record Ftr (cA cB : Cat) : Set (ℓo cA ⊔ ℓh cA ⊔ ℓo cB ⊔ ℓh cB) where
  constructor ftr
  field
    {obj} : (x : Obj cA) → Obj cB
    hom : ∀{x y} → (φ : Hom cA x y) → Hom cB (obj x) (obj y)
    --{{isFtr}} : IsFtr cA cB hom
    .{{hom-id}} : ∀{x} → hom (id⟨ x ⟩) ≡ id
    .{{hom-comp}} : ∀{x y z} (ψ : Hom cA y z) (φ : Hom cA x y) → hom (ψ ∘ φ) ≡ hom ψ ∘ hom φ
open Ftr public
_c→_ = Ftr
infix 1 _c→_

c-id : ∀{cA} → (cA c→ cA)
c-id = ftr f-id

_c∘_ : ∀ {cA cB cC : Cat} → (cB c→ cC) → (cA c→ cB) → (cA c→ cC)
obj (cg c∘ cf) = obj cg f∘ obj cf
hom (cg c∘ cf) = hom cg f∘ hom cf
hom-id (cg c∘ cf) = begin
          hom cg (hom cf id)
            ≡⟨ cong (hom cg) (hom-id cf) ⟩
          hom cg id
            ≡⟨ hom-id cg ⟩
          id ∎
hom-comp (cg c∘ cf) ψ φ = begin
          hom cg (hom cf (ψ ∘ φ))
            ≡⟨ cong (hom cg) (hom-comp cf ψ φ) ⟩
          hom cg (hom cf ψ ∘ hom cf φ)
            ≡⟨ hom-comp cg (hom cf ψ) (hom cf φ) ⟩
          hom cg (hom cf ψ) ∘ hom cg (hom cf φ) ∎

cConst : ∀{cA cB} → Obj cB → (cA c→ cB)
obj (cConst b) x = b
hom (cConst b) φ = id
hom-id (cConst b) = refl
hom-comp (cConst b) ψ φ = sym (lunit id)

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
    .{{nat}} : ∀{x y} → (φ : Hom cA x y) → hom cg φ ∘ obj x ≡ obj y ∘ hom cf φ
open NT public
_nt→_ = NT
infix 1 _nt→_

ext-nt : ∀{cA cB : Cat} {cf cg : cA c→ cB} {nta ntb : cf nt→ cg} → (obj nta ≡ obj ntb) → nta ≡ ntb
ext-nt {cA} {cB} {cf} {cg} {nt .(obj ntb)} {ntb} refl = refl

nt-id : ∀{cA cB} {cf : cA c→ cB} → (cf nt→ cf)
obj (nt-id {cA} {cB} {cf}) a = id
nat (nt-id {cA} {cB} {cf}) φ = begin
          hom cf φ ∘ id
            ≡⟨ runit _ ⟩
          hom cf φ
            ≡⟨ sym (lunit _) ⟩
          id ∘ hom cf φ ∎

nt-id⟨_⟩ : ∀{cA cB} (cf : cA c→ cB) → (cf nt→ cf)
nt-id⟨ _ ⟩ = nt-id

_nt∘_ : ∀{cA cB} {cf cg ch : cA c→ cB} (ntb : cg nt→ ch) (nta : cf nt→ cg) → (cf nt→ ch)
obj (_nt∘_ {cA} {cB} {cf} {cg} {ch} ntb nta) a = obj ntb a ∘ obj nta a
nat (_nt∘_ {cA} {cB} {cf} {cg} {ch} ntb nta) {x}{y} φ = begin
          hom ch φ ∘ (obj ntb x ∘ obj nta x)
            ≡⟨ sym (assoc _ _ _) ⟩
          (hom ch φ ∘ obj ntb x) ∘ obj nta x
            ≡⟨ cong (λ ψ → ψ ∘ (obj nta x)) (nat ntb φ) ⟩
          (obj ntb y ∘ hom cg φ) ∘ obj nta x
            ≡⟨ assoc _ _ _ ⟩
          obj ntb y ∘ (hom cg φ ∘ obj nta x)
            ≡⟨ cong (λ ψ → obj ntb y ∘ ψ) (nat nta φ) ⟩
          obj ntb y ∘ (obj nta y ∘ hom cf φ)
            ≡⟨ sym (assoc _ _ _) ⟩
          (obj ntb y ∘ obj nta y) ∘ hom cf φ ∎

_nt⊚_ : ∀{cA cB cC} {cf cg : cA c→ cB} {ch ck : cB c→ cC} (ntb : ch nt→ ck) (nta : cf nt→ cg) → (ch c∘ cf nt→ ck c∘ cg)
obj (_nt⊚_ {cA} {cB} {cC} {cf} {cg} {ch} {ck} ntb nta) a =
  {-  h f a  →[h nta a]→  h g a  →[ntb g a]→  k g a  -}
  obj ntb (obj cg a) ∘ hom ch (obj nta a)
nat (_nt⊚_ {cA} {cB} {cC} {cf} {cg} {ch} {ck} ntb nta) {a}{b} φ = begin
  {-  h f a  →[h nta a]→  h g a  →[ntb g a]→  k g a  -}
  {-    ↓                     ↓                     ↓     -}
  {- [h f φ]               [h g φ]               [k g φ] -}
  {-    ↓                     ↓                     ↓     -}
  {-  h f b  →[h nta b]→  h g b  →[ntb g b]→  k g b  -}
  hom ck (hom cg φ) ∘ (obj ntb (obj cg a) ∘ hom ch (obj nta a))
    ≡⟨ sym (assoc _ _ _) ⟩
  (hom ck (hom cg φ) ∘ obj ntb (obj cg a)) ∘ hom ch (obj nta a)
    ≡⟨ cong (λ ψ → ψ ∘ _) (nat ntb (hom cg φ)) ⟩
  (obj ntb (obj cg b) ∘ hom ch (hom cg φ)) ∘ hom ch (obj nta a)
    ≡⟨ assoc _ _ _ ⟩
  obj ntb (obj cg b) ∘ (hom ch (hom cg φ) ∘ hom ch (obj nta a))
    ≡⟨ cong (λ ψ → _ ∘ ψ) (begin
       hom ch (hom cg φ) ∘ hom ch (obj nta a)
         ≡⟨ sym (hom-comp ch _ _) ⟩
       hom ch (hom cg φ ∘ obj nta a)
         ≡⟨ cong (hom ch) (nat nta φ) ⟩
       hom ch (obj nta b ∘ hom cf φ)
         ≡⟨ hom-comp ch _ _ ⟩
       hom ch (obj nta b) ∘ hom ch (hom cf φ)
         ∎) ⟩
  obj ntb (obj cg b) ∘ (hom ch (obj nta b) ∘ hom ch (hom cf φ))
    ≡⟨ sym (assoc _ _ _) ⟩
  (obj ntb (obj cg b) ∘ hom ch (obj nta b)) ∘ hom ch (hom cf φ) ∎
