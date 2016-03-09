module willow.cat.Locpath.Composition where

open import willow.cat.RawZigzag public
open import willow.cat.Locpath.Definition public
open import willow.cat.Locpath.Tools public

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
