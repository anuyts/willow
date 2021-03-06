module willow.cat.Groupoid where

open import willow.cat.Isomorphism public
open import willow.cat.Locpath public
open import willow.cat.Opposite public

--NOTE: INSTEAD OF IMPLEMENTING LOCALIZATION AND CORE, IMPLEMENT UNITARIZATION AND UNITARY CORE

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
  Iso.fwd (asIso φ) = φ
  Iso.bck (asIso φ) = inv φ
  Iso.src-id (asIso φ) = src-id φ
  Iso.tgt-id (asIso φ) = tgt-id φ
  
  c-inv : cOp cat ++> cat
  f.obj c-inv = idf
  f.hom c-inv = inv
  f.hom-id' c-inv x = inv-id cat x (asIso (c.id cat x)) refl
  f.hom-m∘' c-inv φ ψ = inv-m∘ cat (asIso ψ) (asIso φ) (asIso (cat $ ψ m∘ φ)) refl
module g = Groupoid

cCore : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Cat ℓo ℓh
c.Obj (cCore c) = c.Obj c
c.Hom (cCore c) x y = Iso c x y
c.id (cCore c) x = i-id c x
c.comp (cCore c) ψ φ = c $ ψ i∘ φ
c.m∘assoc' (cCore c) = ≅ext (c.m∘assoc' c)
c.m∘lunit' (cCore c) = ≅ext (c.m∘lunit' c)
c.m∘runit' (cCore c) = ≅ext (c.m∘runit' c)

coreIsGrpd : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → IsGrpd (cCore c)
≅.fwd (prl (coreIsGrpd c φ)) = φ
≅.bck (prl (coreIsGrpd c φ)) = i-inv c φ
≅.src-id (prl (coreIsGrpd c φ)) = ≅ext (≅.src-id φ)
≅.tgt-id (prl (coreIsGrpd c φ)) = ≅ext (≅.tgt-id φ)
prr (coreIsGrpd c {x}{y} φ) = refl

gCore : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Groupoid ℓo ℓh
g.cat(gCore c) = cCore c
g.isGrpd(gCore c) = coreIsGrpd c

--core is right adjoint to forgetful functor Grpd → Cat
--core is a comonad
--Grpd type with grpd module

cLoc : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Cat ℓo (ℓo ⊔ ℓh)
c.Obj (cLoc c) = c.Obj c
c.Hom (cLoc c) x y = Locpath c x y
c.id (cLoc c) x = mk-lp rz-refl
c.comp (cLoc c) lpb lpa = lpa lp• lpb
c.m∘assoc' (cLoc c) {ψ = lpc}{lpb}{lpa} = sym (lp•assoc lpa lpb lpc)
c.m∘lunit' (cLoc c) = lp•runit _
c.m∘runit' (cLoc c) = lp•lunit _

locIsGrpd : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → IsGrpd (cLoc c)
≅.fwd (prl (locIsGrpd c φ)) = φ
≅.bck (prl (locIsGrpd c φ)) = lp-inv φ
≅.src-id (prl (locIsGrpd c φ)) = lp-src-eq φ
≅.tgt-id (prl (locIsGrpd c φ)) = lp-tgt-eq φ
prr (locIsGrpd c {x}{y} φ) = refl

gLoc : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Groupoid ℓo (ℓo ⊔ ℓh)
g.cat(gLoc c) = cLoc c
g.isGrpd(gLoc c) = locIsGrpd c

f-hom-inv : ∀{ℓoA ℓhA ℓoB ℓhB}
  (gA : Groupoid ℓoA ℓhA) (gB : Groupoid ℓoB ℓhB)
  (cf : g.cat gA ++> g.cat gB)
  {x y : g.Obj gA} (φ : g.Hom gA x y)
  → f.hom cf (g.inv gA φ) == g.inv gB (f.hom cf φ)
f-hom-inv gA gB cf φ =
  let η = g.asIso gA φ
      θ = g.asIso gB (f.hom cf φ)
      p : map≅ cf η == θ
      p = ≅ext refl
  in map= ≅.bck p
