module willow.cat.Groupoid where

open import willow.cat.Isomorphism public
open import willow.cat.Locpath public
open import willow.cat.Opposite public

IsGrpd : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Set (ℓh ⊔ ℓo)
IsGrpd c = {x y : c.Obj c} → (φ : c.Hom c x y) → IsIso c φ

is¶IsGrpd : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Is¶ (IsGrpd c)
is¶IsGrpd c = λ¶i x => λ¶i y => λ¶ φ => is¶IsIso φ

--Groupoid : (ℓo ℓh : Level) → Set (lsuc (ℓo ⊔ ℓh))
--Groupoid ℓo ℓh = Sum λ (c : Cat ℓo ℓh) → IsGrpd c

record Groupoid (ℓo ℓh : Level) : Set (lsuc (ℓo ⊔ ℓh)) where
  no-eta-equality
  constructor mk-grpd
  field
    cat : Cat ℓo ℓh
    isGrpd : IsGrpd cat

  open Cat cat public
  
  private
    asIsoPriv : ∀{x y : Obj} → (φ : Hom x y) → Iso cat x y
    asIsoPriv φ = prl (isGrpd φ)

  inv : ∀{x y : Obj} → (φ : Hom x y) → Hom y x
  inv φ = ≅.bck (asIsoPriv φ)

  src-id : ∀{x y : Obj} → (φ : Hom x y) → cat $ (inv φ) m∘ φ == c.id cat x
  src-id φ = tra (λ ξ → cat $ (inv φ) m∘ ξ == c.id cat _) / prr (isGrpd φ) of ≅.src-id (asIsoPriv φ)

  tgt-id : ∀{x y : Obj} → (φ : Hom x y) → cat $ φ m∘ (inv φ) == c.id cat y
  tgt-id φ = tra (λ ξ → cat $ ξ m∘ (inv φ) == c.id cat _) / prr (isGrpd φ) of ≅.tgt-id (asIsoPriv φ)

  asIso : ∀{x y : Obj} → (φ : Hom x y) → Iso cat x y
  asIso φ = record
        { fwd = φ
        ; bck = inv φ
        ; src-id = src-id φ
        ; tgt-id = tgt-id φ
        }

  c-inv : cOp cat ++> cat
  c-inv = record
    { obj = idf
    ; hom = λ φ → inv φ
    ; hom-id = λ x → inv-id cat x (asIso (c.id cat x)) refl
    ; hom-m∘ = λ φ ψ → inv-m∘ cat (asIso ψ) (asIso φ) (asIso (cat $ ψ m∘ φ)) refl
    }
module g = Groupoid

cCore : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Cat ℓo ℓh
cCore c = record
  { Obj = c.Obj c
  ; Hom = λ x y → Iso c x y
  ; id = λ x → i-id c x
  ; comp = λ ψ φ → c $ ψ i∘ φ
  ; m∘assoc = λ {w x y z ψ ξ φ} → ≅ext (c.m∘assoc c)
  ; m∘lunit = ≅ext (c.m∘lunit c)
  ; m∘runit = ≅ext (c.m∘runit c)
  }

coreIsGrpd : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → IsGrpd (cCore c)
prl (coreIsGrpd c {x}{y} φ) = record
  { fwd = φ
  ; bck = i-inv c φ
  ; src-id = ≅ext (≅.src-id φ)
  ; tgt-id = ≅ext (≅.tgt-id φ)
  }
prr (coreIsGrpd c {x}{y} φ) = refl

--core is right adjoint to forgetful functor Grpd → Cat
--core is a comonad
--Grpd type with grpd module

cLoc : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Cat ℓo (ℓo ⊔ ℓh)
cLoc c = record
  { Obj = c.Obj c
  ; Hom = λ x y → Locpath c x y
  ; id = λ x → mk-lp rz-refl
  ; comp = λ lpa lpb → lpb lp• lpa
  ; m∘assoc = λ {w x y z ψ ξ φ} → sym (lp•assoc φ ξ ψ)
  ; m∘lunit = lp•runit _
  ; m∘runit = lp•lunit _
  }

locIsGrpd : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → IsGrpd (cLoc c)
prl (locIsGrpd c {x}{y} φ) = record
  { fwd = φ
  ; bck = lp-inv φ
  ; src-id = lp-src-eq φ
  ; tgt-id = lp-tgt-eq φ
  }
prr (locIsGrpd c {x}{y} φ) = refl
