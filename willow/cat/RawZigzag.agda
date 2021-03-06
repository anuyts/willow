module willow.cat.RawZigzag where

open import willow.cat.Category public

data RawZigzag {ℓo ℓh} (c : Cat ℓo ℓh) (x : c.Obj c) : (y : c.Obj c) → Set (ℓo ⊔ ℓh) where
  rz-refl : RawZigzag c x x
  _rz>_ : {y z : c.Obj c} → (rz : RawZigzag c x y) → (φ : c.Hom c y z) → RawZigzag c x z
  _rz<_ : {y z : c.Obj c} → (rz : RawZigzag c x y) → (φ : c.Hom c z y) → RawZigzag c x z

infixl 10 _rz>_ _rz<_

_rz•_ : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} → (RawZigzag c x y) → (RawZigzag c y z) → (RawZigzag c x z)
rz rz• rz-refl = rz
rz rz• (rz' rz> φ) = (rz rz• rz') rz> φ
rz rz• (rz' rz< φ) = (rz rz• rz') rz< φ
infixl 10 _rz•_

rz-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (RawZigzag c x y) → (RawZigzag c y x)
rz-inv rz-refl = rz-refl
rz-inv (rz rz> φ) = (rz-refl rz< φ) rz• rz-inv rz
rz-inv (rz rz< φ) = (rz-refl rz> φ) rz• rz-inv rz

----working with composition----------------------

rz-fwd : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c x y → RawZigzag c x y
rz-fwd φ = rz-refl rz> φ

rz-bck : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c y x → RawZigzag c x y
rz-bck φ = rz-refl rz< φ

detach-fwd : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz : RawZigzag c x y) → (φ : c.Hom c y z) → rz rz> φ == rz rz• rz-fwd φ
detach-fwd rz φ = refl

detach-bck : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz : RawZigzag c x y) → (φ : c.Hom c z y) → rz rz< φ == rz rz• rz-bck φ
detach-bck rz φ = refl

rz•assoc : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c}
  → (rz-l : RawZigzag c w x) → (rz-m : RawZigzag c x y) → (rz-r : RawZigzag c y z)
  → (rz-l rz• rz-m) rz• rz-r == rz-l rz• (rz-m rz• rz-r)
rz•assoc rz-l rz-m rz-refl = refl
rz•assoc rz-l rz-m (rz-r rz> φ) = map= (λ rz → rz rz> φ) (rz•assoc rz-l rz-m rz-r)
rz•assoc rz-l rz-m (rz-r rz< φ) = map= (λ rz → rz rz< φ) (rz•assoc rz-l rz-m rz-r)

-----some lemmas------------------------

rz•lunit : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rz : RawZigzag c x y) → (rz-refl rz• rz == rz)
rz•lunit rz-refl = refl
rz•lunit (rz rz> φ) = map= (λ rz' → rz' rz> φ) (rz•lunit rz)
rz•lunit (rz rz< φ) = map= (λ rz' → rz' rz< φ) (rz•lunit rz)

precomp-twice-fwd : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c} → (rz : RawZigzag c y z) → (ψ : c.Hom c x y) → (φ : c.Hom c w x) → (rz-refl rz> φ rz• (rz-refl rz> ψ rz• rz)) == (rz-refl rz> φ rz> ψ rz• rz)
precomp-twice-fwd rz-refl ψ φ = refl
precomp-twice-fwd (rz rz> ξ) ψ φ = map= (λ rz' → rz' rz> ξ) (precomp-twice-fwd rz ψ φ)
precomp-twice-fwd (rz rz< ξ) ψ φ = map= (λ rz' → rz' rz< ξ) (precomp-twice-fwd rz ψ φ)

precomp-twice-bck : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c} → (rz : RawZigzag c y z) → (ψ : c.Hom c y x) → (φ : c.Hom c x w) → (rz-refl rz< φ rz• (rz-refl rz< ψ rz• rz)) == (rz-refl rz< φ rz< ψ rz• rz)
precomp-twice-bck rz-refl ψ φ = refl
precomp-twice-bck (rz rz> ξ) ψ φ = map= (λ rz' → rz' rz> ξ) (precomp-twice-bck rz ψ φ)
precomp-twice-bck (rz rz< ξ) ψ φ = map= (λ rz' → rz' rz< ξ) (precomp-twice-bck rz ψ φ)

precomp-twice-up : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c} → (rz : RawZigzag c y z) → (ψ : c.Hom c y x) → (φ : c.Hom c w x) → (rz-refl rz> φ rz• (rz-refl rz< ψ rz• rz)) == (rz-refl rz> φ rz< ψ rz• rz)
precomp-twice-up rz-refl ψ φ = refl
precomp-twice-up (rz rz> ξ) ψ φ = map= (λ rz' → rz' rz> ξ) (precomp-twice-up rz ψ φ)
precomp-twice-up (rz rz< ξ) ψ φ = map= (λ rz' → rz' rz< ξ) (precomp-twice-up rz ψ φ)

precomp-twice-dn : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c} → (rz : RawZigzag c y z) → (ψ : c.Hom c x y) → (φ : c.Hom c x w) → (rz-refl rz< φ rz• (rz-refl rz> ψ rz• rz)) == (rz-refl rz< φ rz> ψ rz• rz)
precomp-twice-dn rz-refl ψ φ = refl
precomp-twice-dn (rz rz> ξ) ψ φ = map= (λ rz' → rz' rz> ξ) (precomp-twice-dn rz ψ φ)
precomp-twice-dn (rz rz< ξ) ψ φ = map= (λ rz' → rz' rz< ξ) (precomp-twice-dn rz ψ φ)

rz-inv-rz• : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-l : RawZigzag c x y) → (rz-r : RawZigzag c y z)
  → rz-inv (rz-l rz• rz-r) == (rz-inv rz-r) rz• (rz-inv rz-l)
rz-inv-rz• rz-l rz-refl = sym (rz•lunit (rz-inv rz-l))
rz-inv-rz• rz-l (rz-r rz> φ) =
  {-IDEA
    (rzl • (rzr, φ))-1 := ((rzl • rzr), φ)-1 := (φ*) • (rzl • rzr)-1
    = (φ*) • (rzr-1 • rzl-1)
    = ((φ*) • rzr-1) • rzl-1
    =: (rzr, φ)-1 • rzl-1
  -}
  via (rz-bck φ) rz• rz-inv (rz-l rz• rz-r) $ refl •
  via (rz-bck φ) rz• (rz-inv rz-r rz• rz-inv rz-l) $
    map= (λ rz → (rz-bck φ) rz• rz) (rz-inv-rz• rz-l rz-r) •
  sym (rz•assoc (rz-bck φ) (rz-inv rz-r) (rz-inv rz-l))
rz-inv-rz• rz-l (rz-r rz< φ) =
  via (rz-fwd φ) rz• rz-inv (rz-l rz• rz-r) $ refl •
  via (rz-fwd φ) rz• (rz-inv rz-r rz• rz-inv rz-l) $
    map= (λ rz → (rz-fwd φ) rz• rz) (rz-inv-rz• rz-l rz-r) •
  sym (rz•assoc (rz-fwd φ) (rz-inv rz-r) (rz-inv rz-l))

rz-inv-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (rz : RawZigzag c x y) → rz-inv (rz-inv rz) == rz
rz-inv-inv rz-refl = refl
rz-inv-inv (rz rz> φ) =
  {-IDEA
    (rz, φ)-1-1 := ((φ*) • rz -1)-1
    = rz -1-1 • (φ*)-1 = rz • (φ*)-1 =: (rz, φ)
  -}
  via rz-inv(rz-bck φ rz• rz-inv rz) $ refl •
  via rz-inv(rz-inv rz) rz• rz-inv(rz-bck φ) $ rz-inv-rz• (rz-bck φ) (rz-inv rz) •
  via rz rz• rz-fwd φ $ map= (λ rz' → rz' rz• rz-fwd φ) (rz-inv-inv rz) •
  refl
rz-inv-inv (rz rz< φ) =
  via rz-inv(rz-fwd φ rz• rz-inv rz) $ refl •
  via rz-inv(rz-inv rz) rz• rz-inv(rz-fwd φ) $ rz-inv-rz• (rz-fwd φ) (rz-inv rz) •
  via rz rz• rz-bck φ $ map= (λ rz' → rz' rz• rz-bck φ) (rz-inv-inv rz) •
  refl

--mapping zigzags---------------------------

mapRawZigzag : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB) → {x y : c.Obj cA} → (rz : RawZigzag cA x y) → RawZigzag cB (f.obj cf x) (f.obj cf y)
mapRawZigzag cf rz-refl = rz-refl
mapRawZigzag cf (rz rz> φ) = mapRawZigzag cf rz rz> f.hom cf φ
mapRawZigzag cf (rz rz< φ) = mapRawZigzag cf rz rz< f.hom cf φ

map-rz• : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB) → {x y z : c.Obj cA} → (rz-l : RawZigzag cA x y) → (rz-r : RawZigzag cA y z) → mapRawZigzag cf (rz-l rz• rz-r) == mapRawZigzag cf rz-l rz• mapRawZigzag cf rz-r
map-rz• cf rz-l rz-refl = refl
map-rz• cf rz-l (rz-r rz> φ) = map= (λ rz → rz rz> f.hom cf φ) (map-rz• cf rz-l rz-r)
map-rz• cf rz-l (rz-r rz< φ) = map= (λ rz → rz rz< f.hom cf φ) (map-rz• cf rz-l rz-r)

mapRawZigzag-id : ∀{ℓoA ℓhA} → (c : Cat ℓoA ℓhA) → {x y : c.Obj c} → (rz : RawZigzag c x y)
  → mapRawZigzag (c-id c) rz == rz
mapRawZigzag-id c rz-refl = refl
mapRawZigzag-id c (rz rz> φ) = map= (λ rz' → rz' rz> φ) (mapRawZigzag-id c rz)
mapRawZigzag-id c (rz rz< φ) = map= (λ rz' → rz' rz< φ) (mapRawZigzag-id c rz)

mapRawZigzag-c∘ : ∀{ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → {cC : Cat ℓoC ℓhC}
  → (cg : cB ++> cC) → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (rz : RawZigzag cA x y)
  → mapRawZigzag (cg c∘ cf) rz == mapRawZigzag cg (mapRawZigzag cf rz)
mapRawZigzag-c∘ cg cf rz-refl = refl
mapRawZigzag-c∘ cg cf (rz rz> φ) = map= (λ rz' → rz' rz> f.hom (cg c∘ cf) φ) (mapRawZigzag-c∘ cg cf rz)
mapRawZigzag-c∘ cg cf (rz rz< φ) = map= (λ rz' → rz' rz< f.hom (cg c∘ cf) φ) (mapRawZigzag-c∘ cg cf rz)

map-rz-inv : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (rz : RawZigzag cA x y)
  → mapRawZigzag cf (rz-inv rz) == rz-inv (mapRawZigzag cf rz)
map-rz-inv cf rz-refl = refl
map-rz-inv cf (rz rz> φ) =
  map-rz• cf (rz-refl rz< φ) (rz-inv rz) •
  map= (λ rz' → (rz-refl rz< f.hom cf φ) rz• rz') (map-rz-inv cf rz)
map-rz-inv cf (rz rz< φ) = 
  map-rz• cf (rz-refl rz> φ) (rz-inv rz) •
  map= (λ rz' → (rz-refl rz> f.hom cf φ) rz• rz') (map-rz-inv cf rz)
