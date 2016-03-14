module willow.cat.Zigzag.Definition where

open import willow.cat.RawZigzag public

----defining locpaths-----------------------------

private
  data Zigzag' {ℓo ℓh} (c : Cat ℓo ℓh) (x y : c.Obj c) : Set (ℓo ⊔ ℓh) where
    mk-zz' : RawZigzag c x y → Zigzag' c x y
    
Zigzag = Zigzag'

data EqZigzag {ℓo ℓh} (c : Cat ℓo ℓh) {x : c.Obj c} : {y : c.Obj c} → (rza rzb : RawZigzag c x y) → Set (ℓo ⊔ ℓh) where
  zz-refl : {y : c.Obj c} → {rz : RawZigzag c x y} → EqZigzag c rz rz
  zz-id-fwd : {y : c.Obj c} → {rz : RawZigzag c x y} → EqZigzag c (rz rz> (c.id c y)) rz
  zz-id-bck : {y : c.Obj c} → {rz : RawZigzag c x y} → EqZigzag c (rz rz< (c.id c y)) rz
  zz-comp-fwd : {y z w : c.Obj c} → {rz : RawZigzag c x y} → {φ : c.Hom c y z} → {ψ : c.Hom c z w}
    → EqZigzag c (rz rz> φ rz> ψ) (rz rz> (c $ ψ m∘ φ))
  zz-comp-bck : {y z w : c.Obj c} → {rz : RawZigzag c x y} → {φ : c.Hom c z y} → {ψ : c.Hom c w z}
    → EqZigzag c (rz rz< φ rz< ψ) (rz rz< (c $ φ m∘ ψ))
  zz-cong-fwd : {y z : c.Obj c} → {rz rz' : RawZigzag c x y} → EqZigzag c rz rz' → {φ : c.Hom c y z}
    → EqZigzag c (rz rz> φ) (rz' rz> φ)
  zz-cong-bck : {y z : c.Obj c} → {rz rz' : RawZigzag c x y} → EqZigzag c rz rz' → {φ : c.Hom c z y}
    → EqZigzag c (rz rz< φ) (rz' rz< φ)

mk-zz : ∀{ℓo ℓh} → {c : Cat ℓo ℓh} → {x y : c.Obj c} → (RawZigzag c x y) → Zigzag c x y
mk-zz rz = mk-zz' rz

postulate eq-zz : ∀{ℓo ℓh} → {c : Cat ℓo ℓh} → {x y : c.Obj c} → {rz rz' : RawZigzag c x y} → (EqZigzag c rz rz') → (mk-zz rz == mk-zz rz')

elim-zz : ∀{ℓo ℓh ℓB} → {c : Cat ℓo ℓh} → {x : c.Obj c}
  → (B : (y : c.Obj c) → Set ℓB)
  → (f : (y : c.Obj c) → RawZigzag c x y → B y)
  → (f-eq : (y : c.Obj c) → (rz rz' : RawZigzag c x y) → (EqZigzag c rz rz') → f y rz == f y rz')
  → {y : c.Obj c} → (zz : Zigzag c x y) → B y
elim-zz {_}{_}{_} {c} {x} B f f-eq {y} (mk-zz' rz) = f y rz

elimd-zz : ∀{ℓo ℓh ℓB} → {c : Cat ℓo ℓh} → {x : c.Obj c}
  → (B : (y : c.Obj c) → (zz : Zigzag c x y) → Set ℓB)
  → (f : (y : c.Obj c) → (rz : RawZigzag c x y) → B y (mk-zz rz))
  → (f-eq : (y : c.Obj c) → (rz rz' : RawZigzag c x y) → (p : EqZigzag c rz rz') → tra (B y) / eq-zz p of f y rz == f y rz')
  → {y : c.Obj c} → (zz : Zigzag c x y) → B y zz
elimd-zz {_}{_}{_} {c} {x} B f f-eq {y} (mk-zz' rz) = f y rz
