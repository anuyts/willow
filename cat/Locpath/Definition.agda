module willow.cat.Locpath.Definition where

open import willow.cat.RawZigzag public

----defining locpaths-----------------------------

private
  data Locpath' {ℓo ℓh} (c : Cat ℓo ℓh) (x y : c.Obj c) : Set (ℓo ⊔ ℓh) where
    mk-lp' : RawZigzag c x y → Locpath' c x y

Locpath = Locpath'

data EqLocpath {ℓo ℓh} (c : Cat ℓo ℓh) {x : c.Obj c} : {y : c.Obj c} → (rza rzb : RawZigzag c x y) → Set (ℓo ⊔ ℓh) where
  lp-refl : {y : c.Obj c} → {rz : RawZigzag c x y} → EqLocpath c rz rz
  lp-id-fwd : {y : c.Obj c} → {rz : RawZigzag c x y} → EqLocpath c (rz rz> (c.id c y)) rz
  lp-id-bck : {y : c.Obj c} → {rz : RawZigzag c x y} → EqLocpath c (rz rz< (c.id c y)) rz
  lp-comp-fwd : {y z w : c.Obj c} → {rz : RawZigzag c x y} → {φ : c.Hom c y z} → {ψ : c.Hom c z w}
    → EqLocpath c (rz rz> φ rz> ψ) (rz rz> (c $ ψ m∘ φ))
  lp-comp-bck : {y z w : c.Obj c} → {rz : RawZigzag c x y} → {φ : c.Hom c z y} → {ψ : c.Hom c w z}
    → EqLocpath c (rz rz< φ rz< ψ) (rz rz< (c $ φ m∘ ψ))
  lp-cancel-up : {y z : c.Obj c} → {rz : RawZigzag c x y} → {φ : c.Hom c y z}
    → EqLocpath c (rz rz> φ rz< φ) rz
  lp-cancel-dn : {y z : c.Obj c} → {rz : RawZigzag c x y} → {φ : c.Hom c z y}
    → EqLocpath c (rz rz< φ rz> φ) rz
  lp-cong-fwd : {y z : c.Obj c} → {rz rz' : RawZigzag c x y} → EqLocpath c rz rz' → {φ : c.Hom c y z}
    → EqLocpath c (rz rz> φ) (rz' rz> φ)
  lp-cong-bck : {y z : c.Obj c} → {rz rz' : RawZigzag c x y} → EqLocpath c rz rz' → {φ : c.Hom c z y}
    → EqLocpath c (rz rz< φ) (rz' rz< φ)

mk-lp : ∀{ℓo ℓh} → {c : Cat ℓo ℓh} → {x y : c.Obj c} → (RawZigzag c x y) → Locpath c x y
mk-lp rz = mk-lp' rz

postulate eq-lp : ∀{ℓo ℓh} → {c : Cat ℓo ℓh} → {x y : c.Obj c} → {rz rz' : RawZigzag c x y} → (EqLocpath c rz rz') → (mk-lp rz == mk-lp rz')

elim-lp : ∀{ℓo ℓh ℓB} → {c : Cat ℓo ℓh} → {x : c.Obj c}
  → (B : (y : c.Obj c) → Set ℓB)
  → (f : (y : c.Obj c) → RawZigzag c x y → B y)
  → (f-eq : (y : c.Obj c) → (rz rz' : RawZigzag c x y) → (EqLocpath c rz rz') → f y rz == f y rz')
  → {y : c.Obj c} → (lp : Locpath c x y) → B y
elim-lp {_}{_}{_} {c} {x} B f f-eq {y} (mk-lp' rz) = f y rz

elimd-lp : ∀{ℓo ℓh ℓB} → {c : Cat ℓo ℓh} → {x : c.Obj c}
  → (B : (y : c.Obj c) → (lp : Locpath c x y) → Set ℓB)
  → (f : (y : c.Obj c) → (rz : RawZigzag c x y) → B y (mk-lp rz))
  → (f-eq : (y : c.Obj c) → (rz rz' : RawZigzag c x y) → (p : EqLocpath c rz rz') → tra (B y) / eq-lp p of f y rz == f y rz')
  → {y : c.Obj c} → (lp : Locpath c x y) → B y lp
elimd-lp {_}{_}{_} {c} {x} B f f-eq {y} (mk-lp' rz) = f y rz
