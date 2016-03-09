module willow.cat.Locpath where

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
  → (B : (y : c.Obj c) → (Locpath c x y) → Set ℓB)
  → (f : (y : c.Obj c) → (rz : RawZigzag c x y) → B y (mk-lp rz))
  → (f-eq : (y : c.Obj c) → (rz rz' : RawZigzag c x y) → (p : EqLocpath c rz rz') → tra (B y) / eq-lp p of f y rz == f y rz')
  → {y : c.Obj c} → (lp : Locpath c x y) → B y lp
elimd-lp {_}{_}{_} {c} {x} B f f-eq {y} (mk-lp' rz) = f y rz

---------------auxiliary-----------------------------------------

lp-nil : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x : c.Obj c} → Locpath c x x
lp-nil = mk-lp rz-refl

pre-lp> : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} (lp : Locpath c x y) {z : c.Obj c} (φ : c.Hom c y z) → Locpath c x z
pre-lp> {ℓo}{ℓh}{c}{x} = elim-lp
  (λ y → {z : c.Obj c} (φ : c.Hom c y z) → Locpath c x z)
  (λ y rz φ → mk-lp (rz rz> φ))
  (λ y rz rz' p → λi= z => λ= φ => eq-lp (lp-cong-fwd p))

_lp>_ : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} (lp : Locpath c x y) (φ : c.Hom c y z) → Locpath c x z
lp lp> φ = pre-lp> lp φ

pre-lp< : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} (lp : Locpath c x y) {z : c.Obj c} (φ : c.Hom c z y) → Locpath c x z
pre-lp< {ℓo}{ℓh}{c}{x} = elim-lp
  (λ y → {z : c.Obj c} (φ : c.Hom c z y) → Locpath c x z)
  (λ y rz φ → mk-lp (rz rz< φ))
  (λ y rz rz' p → λi= z => λ= φ => eq-lp (lp-cong-bck p))

_lp<_ : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} (lp : Locpath c x y) (φ : c.Hom c z y) → Locpath c x z
lp lp< φ = pre-lp< lp φ

infixl 10 _lp>_ _lp<_

lp-fwd : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c x y → Locpath c x y
lp-fwd φ = mk-lp (rz-fwd φ)

lp-bck : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c y x → Locpath c x y
lp-bck φ = mk-lp (rz-bck φ)

---------------composition of locpaths---------------------------

rz•eq-lp : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-l : RawZigzag c x y) → (rz-ra rz-rb : RawZigzag c y z)
  → EqLocpath c rz-ra rz-rb → (EqLocpath c (rz-l rz• rz-ra) (rz-l rz• rz-rb))
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l rz-r .rz-r lp-refl = lp-refl
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l _ rz-rb lp-id-fwd = lp-id-fwd
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l _ rz-rb lp-id-bck = lp-id-bck
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l _ _ lp-comp-fwd = lp-comp-fwd
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l _ _ lp-comp-bck = lp-comp-bck
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l _ rz-rb lp-cancel-up = lp-cancel-up
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l _ rz-rb lp-cancel-dn = lp-cancel-dn
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l (rz-ra rz> φ) (rz-rb rz> .φ) (lp-cong-fwd p) = lp-cong-fwd (rz•eq-lp rz-l rz-ra rz-rb p)
rz•eq-lp {_}{_} {c} {x}{y}{z} rz-l (rz-ra rz< φ) (rz-rb rz< .φ) (lp-cong-bck p) = lp-cong-bck (rz•eq-lp rz-l rz-ra rz-rb p)

_rz•lp_ : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} → (RawZigzag c x y) → (Locpath c y z) → (Locpath c x z)
_rz•lp_ {_}{_} {c} {x}{y}{z0} rz-l lp-r = elim-lp (λ z → Locpath c x z)
  (λ z rz-r → mk-lp (rz-l rz• rz-r))
  (λ z rz-ra rz-rb p → eq-lp (rz•eq-lp rz-l rz-ra rz-rb p))
  {z0} lp-r

eq-lp•rz : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-la rz-lb : RawZigzag c x y) → (rz-r : RawZigzag c y z)
  → EqLocpath c rz-la rz-lb → (EqLocpath c (rz-la rz• rz-r) (rz-lb rz• rz-r))
eq-lp•rz rz-la rz-lb rz-refl p = p
eq-lp•rz rz-la rz-lb (rz-r rz> φ) p = lp-cong-fwd (eq-lp•rz rz-la rz-lb rz-r p)
eq-lp•rz rz-la rz-lb (rz-r rz< φ) p = lp-cong-bck (eq-lp•rz rz-la rz-lb rz-r p)

eq-lp•lp : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-la rz-lb : RawZigzag c x y) → (lp-r : Locpath c y z)
  → EqLocpath c rz-la rz-lb → ((rz-la rz•lp lp-r) == (rz-lb rz•lp lp-r))
eq-lp•lp {_}{_} {c} {x}{y}{z0} rz-la rz-lb lp-r0 p = elimd-lp {c = c}{x = y}
  (λ z lp-r → (rz-la rz•lp lp-r) == (rz-lb rz•lp lp-r))
  (λ z rz-r → eq-lp (eq-lp•rz rz-la rz-lb rz-r p))
  (λ z rz-ra rz-rb q → uip)
  {z0} lp-r0

_lp•_ : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} → (Locpath c x y) → (Locpath c y z) → (Locpath c x z)
_lp•_ {_}{_} {c} {x}{y0}{z0} lp-l lp-r0 = elim-lp {c = c} {x = x}
  (λ y → (z : c.Obj c) → (Locpath c y z) → (Locpath c x z))
  (λ y rz-l z lp-r → rz-l rz•lp lp-r)
  (λ y rz-la rz-lb p → λ= z => λ= lp-r => eq-lp•lp rz-la rz-lb lp-r p)
  {y0} lp-l z0 lp-r0

--inversion of locpaths----------------------------

eq-lp-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rza rzb : RawZigzag c x y) → (p : EqLocpath c rza rzb) → (EqLocpath c (rz-inv rza) (rz-inv rzb))
eq-lp-inv {_}{_} {c} {x}{y} rz .rz lp-refl = lp-refl
eq-lp-inv {_}{_} {c} {x}{y} .(rzb rz> (c.id c y)) rzb lp-id-fwd =
  tra (λ rz-r' → EqLocpath c (rz-inv (rzb rz> (c.id c y))) rz-r') / (rz•lunit (rz-inv rzb)) of
  eq-lp•rz (rz-refl rz< (c.id c y)) rz-refl (rz-inv rzb) lp-id-bck
eq-lp-inv {_}{_} {c} {x}{y} .(rzb rz< (c.id c y)) rzb lp-id-bck =
  tra (λ rz-r' → EqLocpath c (rz-inv (rzb rz< (c.id c y))) rz-r') / (rz•lunit (rz-inv rzb)) of
  eq-lp•rz (rz-refl rz> (c.id c y)) rz-refl (rz-inv rzb) lp-id-fwd
eq-lp-inv {_}{_} {c} {x}{w} (rz rz> φ rz> ψ) .(rz rz> (c $ ψ m∘ φ)) lp-comp-fwd =
  tra (λ rz-l → EqLocpath c rz-l (rz-inv (rz rz> c $ ψ m∘ φ))) / sym (precomp-twice-bck (rz-inv rz) φ ψ) of
  eq-lp•rz (rz-refl rz< ψ rz< φ) (rz-refl rz< (c $ ψ m∘ φ)) (rz-inv rz) lp-comp-bck
eq-lp-inv {_}{_} {c} {x}{y} (rz rz< φ rz< ψ) .(rz rz< (c $ φ m∘ ψ)) lp-comp-bck = 
  tra (λ rz-l → EqLocpath c rz-l (rz-inv (rz rz< c $ φ m∘ ψ))) / sym (precomp-twice-fwd (rz-inv rz) φ ψ) of
  eq-lp•rz (rz-refl rz> ψ rz> φ) (rz-refl rz> (c $ φ m∘ ψ)) (rz-inv rz) lp-comp-fwd
eq-lp-inv {_}{_} {c} {x}{y} (rz rz> φ rz< .φ) .rz lp-cancel-up = 
  tra (λ rz-l → EqLocpath c rz-l (rz-inv rz)) / sym (precomp-twice-up (rz-inv rz) φ φ) of
  tra (λ rz-r → EqLocpath c (rz-refl rz> φ rz< φ rz• rz-inv rz) rz-r) / rz•lunit (rz-inv rz) of
  eq-lp•rz (rz-refl rz> φ rz< φ) (rz-refl) (rz-inv rz) lp-cancel-up
eq-lp-inv {_}{_} {c} {x}{y} (rz rz< φ rz> .φ) .rz lp-cancel-dn = 
  tra (λ rz-l → EqLocpath c rz-l (rz-inv rz)) / sym (precomp-twice-dn (rz-inv rz) φ φ) of
  tra (λ rz-r → EqLocpath c (rz-refl rz< φ rz> φ rz• rz-inv rz) rz-r) / rz•lunit (rz-inv rz) of
  eq-lp•rz (rz-refl rz< φ rz> φ) (rz-refl) (rz-inv rz) lp-cancel-dn
eq-lp-inv {_}{_} {c} {x}{y} (rza rz> φ) (rzb rz> .φ) (lp-cong-fwd p) =
  rz•eq-lp (rz-refl rz< φ) (rz-inv rza) (rz-inv rzb) (eq-lp-inv rza rzb p)
eq-lp-inv {_}{_} {c} {x}{y} (rza rz< φ) (rzb rz< .φ) (lp-cong-bck p) = 
  rz•eq-lp (rz-refl rz> φ) (rz-inv rza) (rz-inv rzb) (eq-lp-inv rza rzb p)

lp-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (Locpath c x y) → (Locpath c y x)
lp-inv {_}{_}{c}{x} = elim-lp
  (λ y → Locpath c y x)
  (λ y rz → mk-lp (rz-inv rz))
  (λ y rza rzb p → eq-lp (eq-lp-inv rza rzb p))

--associativity of locpath composition------------------

lp•assoc : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c}
  → (lp-l : Locpath c w x) → (lp-m : Locpath c x y) → (lp-r : Locpath c y z)
  → (lp-l lp• lp-m) lp• lp-r == lp-l lp• (lp-m lp• lp-r)
lp•assoc {_}{_}{c} {w}{x0}{y0}{z0} lp-l0 lp-m0 lp-r0 =
  elimd-lp
  (λ x lp-l →
    {y z : c.Obj c} → (lp-m : Locpath c x y) → (lp-r : Locpath c y z)
    → (lp-l lp• lp-m) lp• lp-r == lp-l lp• (lp-m lp• lp-r)
  )
  (λ x rz-l {y1}{z1} lp-m1 lp-r1 →
    elimd-lp
    (λ y lp-m →
      {z : c.Obj c} → (lp-r : Locpath c y z)
      → ((mk-lp rz-l) lp• lp-m) lp• lp-r == (mk-lp rz-l) lp• (lp-m lp• lp-r)
    )
    (λ y rz-m {z2} lp-r2 →
      elimd-lp
      (λ z lp-r → ((mk-lp rz-l) lp• (mk-lp rz-m)) lp• lp-r == (mk-lp rz-l) lp• ((mk-lp rz-m) lp• lp-r))
      (λ z rz-r → map= mk-lp (rz•assoc rz-l rz-m rz-r))
      (λ z rz-r rz-r' p → uip)
      {z2} lp-r2
    )
    (λ y rz-m rz-m' p → λ¶i z => λ¶ lp-r => uip)
    {y1} lp-m1 lp-r1
  )
  (λ x rz-l rz-l' p → λ¶i y => λ¶i z => λ¶ lp-m => λ¶ lp-r => uip)
  {x0} lp-l0 lp-m0 lp-r0

--left and right unit laws-------------------------

lp•lunit : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (lp : Locpath c x y)
  → ((mk-lp rz-refl) lp• lp) == lp
lp•lunit {_}{_}{x} = elimd-lp
  (λ y lp → ((mk-lp rz-refl) lp• lp) == lp)
  (λ y rz → map= mk-lp (rz•lunit rz))
  (λ y rz rz' p → uip)

lp•runit : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (lp : Locpath c x y)
  → (lp lp• (mk-lp rz-refl)) == lp
lp•runit {_}{_}{x} = elimd-lp
  (λ y lp → (lp lp• (mk-lp rz-refl)) == lp)
  (λ y rz → refl)
  (λ y rz rz' p → uip)

--composition of inverse locpaths----------------------

pre-lp-tgt-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rz : RawZigzag c x y)
  → (lp-inv (mk-lp rz)) lp• (mk-lp rz) == mk-lp rz-refl
pre-lp-tgt-eq rz-refl = refl
pre-lp-tgt-eq (rz rz> φ) =
       {-
       idee:
       (rz, φ)-1 • (rz, φ)
       = (φ* • rz-1) • (rz • φ)
       = ((φ* • rz-1) • rz) • φ
       = (φ* • (rz-1 • rz)) • φ
       = (φ* • refl) • φ
       := φ* • φ
       = (φ*, φ)
       = refl
       -}
       via (lp-inv (mk-lp (rz rz> φ)) lp• mk-lp (rz rz> φ)) $ refl •
       via mk-lp (rz-inv (rz rz> φ) rz• rz rz> φ) $ refl •
       via mk-lp ((rz-bck φ rz• rz-inv rz) rz• rz rz> φ) $ refl •
       via mk-lp ((rz-bck φ rz• rz-inv rz) rz• (rz rz• (rz-fwd φ))) $
         map= (λ rz' → mk-lp ((rz-bck φ rz• rz-inv rz) rz• rz')) (detach-fwd rz φ) •
       via mk-lp (((rz-bck φ rz• rz-inv rz) rz• rz) rz• (rz-fwd φ)) $
         map= mk-lp (sym (rz•assoc (rz-bck φ rz• rz-inv rz) rz (rz-fwd φ))) •
       via mk-lp (rz-bck φ rz• (rz-inv rz rz• rz) rz• (rz-fwd φ)) $
         map= (λ rz' → mk-lp (rz' rz• (rz-fwd φ))) (rz•assoc (rz-bck φ) (rz-inv rz) rz) •
       via (mk-lp (rz-bck φ) lp• (lp-inv (mk-lp rz) lp• mk-lp rz)) lp• mk-lp (rz-fwd φ) $ refl •
       via (mk-lp (rz-bck φ) lp• mk-lp rz-refl) lp• mk-lp (rz-fwd φ) $
         map= (λ lp' → (mk-lp (rz-bck φ) lp• lp') lp• mk-lp (rz-fwd φ)) (pre-lp-tgt-eq rz) •
       via mk-lp (rz-bck φ rz• rz-fwd φ) $ refl •
       via mk-lp (rz-refl rz< φ rz> φ) $ refl •
       eq-lp lp-cancel-dn
pre-lp-tgt-eq (rz rz< φ) = 
       via (lp-inv (mk-lp (rz rz< φ)) lp• mk-lp (rz rz< φ)) $ refl •
       via mk-lp (rz-inv (rz rz< φ) rz• rz rz< φ) $ refl •
       via mk-lp ((rz-fwd φ rz• rz-inv rz) rz• rz rz< φ) $ refl •
       via mk-lp ((rz-fwd φ rz• rz-inv rz) rz• (rz rz• (rz-bck φ))) $
         map= (λ rz' → mk-lp ((rz-fwd φ rz• rz-inv rz) rz• rz')) (detach-bck rz φ) •
       via mk-lp (((rz-fwd φ rz• rz-inv rz) rz• rz) rz• (rz-bck φ)) $
         map= (mk-lp) (sym (rz•assoc (rz-fwd φ rz• rz-inv rz) rz (rz-bck φ))) •
       via mk-lp (rz-fwd φ rz• (rz-inv rz rz• rz) rz• (rz-bck φ)) $
         map= (λ rz' → mk-lp (rz' rz• (rz-bck φ))) (rz•assoc (rz-fwd φ) (rz-inv rz) rz) •
       via (mk-lp (rz-fwd φ) lp• (lp-inv (mk-lp rz) lp• mk-lp rz)) lp• mk-lp (rz-bck φ) $ refl •
       via (mk-lp (rz-fwd φ) lp• mk-lp rz-refl) lp• mk-lp (rz-bck φ) $
         map= (λ lp' → (mk-lp (rz-fwd φ) lp• lp') lp• mk-lp (rz-bck φ)) (pre-lp-tgt-eq rz) •
       via mk-lp (rz-fwd φ rz• rz-bck φ) $ refl •
       via mk-lp (rz-refl rz> φ rz< φ) $ refl •
       eq-lp lp-cancel-up

lp-tgt-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (lp : Locpath c x y)
  → (lp-inv lp) lp• lp == mk-lp rz-refl
lp-tgt-eq {_}{_} {c} {x} = elimd-lp
  (λ y lp → (lp-inv lp) lp• lp == mk-lp rz-refl)
  (λ y rz → pre-lp-tgt-eq rz)
  (λ y rz rz' p → uip)

pre-lp-src-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rz : RawZigzag c x y)
  → mk-lp rz lp• lp-inv (mk-lp rz) == mk-lp rz-refl
pre-lp-src-eq rz-refl = refl
pre-lp-src-eq (rz rz> φ) =
  {-
  Idee:
  (r, φ) • (r, φ)-1
  = (r • φ) • (φ* • r-1)
  = ((r • φ) • φ*) • r-1
  = (r • (φ • φ*)) • r-1
  = (r • refl) • r-1
  := r • r-1
  = refl
  -}
  via mk-lp (rz rz> φ) lp• lp-inv (mk-lp (rz rz> φ)) $ refl •
  via mk-lp (rz rz> φ rz• rz-inv (rz rz> φ)) $ refl •
  via mk-lp (rz rz> φ rz• (rz-bck φ rz• rz-inv rz)) $ refl •
  via mk-lp ((rz rz• rz-fwd φ) rz• (rz-bck φ rz• rz-inv rz)) $
    map= (λ rz' → mk-lp (rz' rz• (rz-bck φ rz• rz-inv rz)) ) (detach-fwd rz φ) •
  via mk-lp (((rz rz• rz-fwd φ) rz• rz-bck φ) rz• rz-inv rz) $
    map= mk-lp (sym (rz•assoc (rz rz• rz-fwd φ) (rz-bck φ) (rz-inv rz))) •
  via mk-lp ((rz rz• (rz-fwd φ rz• rz-bck φ)) rz• rz-inv rz) $
    map= (λ rz' → mk-lp (rz' rz• rz-inv rz)) (rz•assoc rz (rz-fwd φ) (rz-bck φ)) •
  via (mk-lp rz lp• mk-lp (rz-fwd φ rz• rz-bck φ)) lp• lp-inv (mk-lp rz) $
    refl •
  via (mk-lp rz lp• mk-lp rz-refl) lp• lp-inv (mk-lp rz) $
    map= (λ lp' → (mk-lp rz lp• lp') lp• lp-inv (mk-lp rz) ) (eq-lp (lp-cancel-up {rz = rz-refl})) •
  via mk-lp (rz rz• rz-inv rz) $ refl •
  pre-lp-src-eq rz
pre-lp-src-eq (rz rz< φ) = 
  via mk-lp (rz rz< φ) lp• lp-inv (mk-lp (rz rz< φ)) $ refl •
  via mk-lp (rz rz< φ rz• rz-inv (rz rz< φ)) $ refl •
  via mk-lp (rz rz< φ rz• (rz-fwd φ rz• rz-inv rz)) $ refl •
  via mk-lp ((rz rz• rz-bck φ) rz• (rz-fwd φ rz• rz-inv rz)) $
    map= (λ rz' → mk-lp (rz' rz• (rz-fwd φ rz• rz-inv rz)) ) (detach-bck rz φ) •
  via mk-lp (((rz rz• rz-bck φ) rz• rz-fwd φ) rz• rz-inv rz) $
    map= mk-lp (sym (rz•assoc (rz rz• rz-bck φ) (rz-fwd φ) (rz-inv rz))) •
  via mk-lp ((rz rz• (rz-bck φ rz• rz-fwd φ)) rz• rz-inv rz) $
    map= (λ rz' → mk-lp (rz' rz• rz-inv rz)) (rz•assoc rz (rz-bck φ) (rz-fwd φ)) •
  via (mk-lp rz lp• mk-lp (rz-bck φ rz• rz-fwd φ)) lp• lp-inv (mk-lp rz) $
    refl •
  via (mk-lp rz lp• mk-lp rz-refl) lp• lp-inv (mk-lp rz) $
    map= (λ lp' → (mk-lp rz lp• lp') lp• lp-inv (mk-lp rz) ) (eq-lp (lp-cancel-dn {rz = rz-refl})) •
  via mk-lp (rz rz• rz-inv rz) $ refl •
  pre-lp-src-eq rz

lp-src-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (lp : Locpath c x y)
  → lp lp• (lp-inv lp) == mk-lp rz-refl
lp-src-eq {_}{_} {c} {x} = elimd-lp
  (λ y lp → lp lp• (lp-inv lp) == mk-lp rz-refl)
  (λ y rz → pre-lp-src-eq rz)
  (λ y rz rz' p → uip)

--mapping locpaths-----------------------------------------

mapEqLocpath : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (rza rzb : RawZigzag cA x y)
  → (EqLocpath cA rza rzb) → EqLocpath cB (mapRawZigzag cf rza) (mapRawZigzag cf rzb)
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} rzb .rzb lp-refl = lp-refl
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} .(rzb rz> c.id cA y) rzb lp-id-fwd =
  tra (λ φ → EqLocpath cB ((mapRawZigzag cf rzb) rz> φ) (mapRawZigzag cf rzb)) / sym (f.hom-id cf _) of lp-id-fwd
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} .(rzb rz< c.id cA y) rzb lp-id-bck = 
  tra (λ φ → EqLocpath cB ((mapRawZigzag cf rzb) rz< φ) (mapRawZigzag cf rzb)) / sym (f.hom-id cf _) of lp-id-bck
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} (rzb rz> φ rz> ψ) .(rzb rz> cA $ ψ m∘ φ) lp-comp-fwd =
  tra
    (λ ξ → EqLocpath cB
      ((mapRawZigzag cf rzb) rz> (f.hom cf φ) rz> (f.hom cf ψ))
      ((mapRawZigzag cf rzb) rz> ξ)
    )
    / sym (f.hom-m∘ cf _ _) of lp-comp-fwd
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} (rzb rz< φ rz< ψ) .(rzb rz< cA $ φ m∘ ψ) lp-comp-bck = 
  tra
    (λ ξ → EqLocpath cB
      ((mapRawZigzag cf rzb) rz< (f.hom cf φ) rz< (f.hom cf ψ))
      ((mapRawZigzag cf rzb) rz< ξ)
    )
    / sym (f.hom-m∘ cf _ _) of lp-comp-bck
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} (rzb rz> φ rz< .φ) .rzb lp-cancel-up = lp-cancel-up
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} (rzb rz< φ rz> .φ) .rzb lp-cancel-dn = lp-cancel-dn
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} _ _ (lp-cong-fwd p) = lp-cong-fwd (mapEqLocpath cf _ _ p)
mapEqLocpath {_}{_}{_}{_} {cA}{cB} cf {x}{y} _ _ (lp-cong-bck p) = lp-cong-bck (mapEqLocpath cf _ _ p)

mapLocpath : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (lp : Locpath cA x y) → Locpath cB (f.obj cf x) (f.obj cf y)
mapLocpath cf {x} = elim-lp
  (λ y → Locpath _ (f.obj cf x) (f.obj cf y))
  (λ y rz → mk-lp (mapRawZigzag cf rz))
  (λ y rz rz' p → eq-lp (mapEqLocpath cf rz rz' p))

map-lp• : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y z : c.Obj cA} → (lp-l : Locpath cA x y) → (lp-r : Locpath cA y z)
  → mapLocpath cf (lp-l lp• lp-r) == mapLocpath cf lp-l lp• mapLocpath cf lp-r
map-lp• {_}{_}{_}{_} {cA}{cB} cf {x}{y0}{z0} lp-l0 lp-r0 = elimd-lp
  (λ y lp-l → {z : c.Obj cA} → (lp-r : Locpath cA y z)
    → mapLocpath cf (lp-l lp• lp-r) == mapLocpath cf lp-l lp• mapLocpath cf lp-r)
  (λ y rz-l {z0} lp-r0 → elimd-lp
    (λ z lp-r → mapLocpath cf (mk-lp rz-l lp• lp-r) == mapLocpath cf (mk-lp rz-l) lp• mapLocpath cf lp-r)
    (λ z rz-r → map= mk-lp (map-rz• cf rz-l rz-r))
    (λ z rz-r rz-r' p → uip)
    {z0} lp-r0
  )
  (λ y rz rz' p → λ¶i z => λ¶ lp-r => uip)
  {y0} lp-l0 {z0} lp-r0

mapLocpath-id : ∀{ℓoA ℓhA} → (c : Cat ℓoA ℓhA) → {x y : c.Obj c} → (lp : Locpath c x y)
  → mapLocpath (c-id c) lp == lp
mapLocpath-id c {x} = elimd-lp
  (λ y lp → mapLocpath (c-id c) lp == lp)
  (λ y rz → map= mk-lp (mapRawZigzag-id c rz))
  (λ y rz rz' p → uip)

mapLocpath-m∘ : ∀{ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → {cC : Cat ℓoC ℓhC}
  → (cg : cB ++> cC) → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (lp : Locpath cA x y)
  → mapLocpath (cg c∘ cf) lp == mapLocpath cg (mapLocpath cf lp)
mapLocpath-m∘ cg cf {x} = elimd-lp
  (λ y lp → mapLocpath (cg c∘ cf) lp == mapLocpath cg (mapLocpath cf lp))
  (λ y rz → map= mk-lp (mapRawZigzag-m∘ cg cf rz))
  (λ y rz rz' p → uip)
