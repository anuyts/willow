module willow.cat.Zigzag.Composition where

open import willow.cat.RawZigzag public
open import willow.cat.Zigzag.Definition public
open import willow.cat.Zigzag.Tools public

---------------composition of locpaths---------------------------

rz•eq-zz : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-l : RawZigzag c x y) → (rz-ra rz-rb : RawZigzag c y z)
  → EqZigzag c rz-ra rz-rb → (EqZigzag c (rz-l rz• rz-ra) (rz-l rz• rz-rb))
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l rz-r .rz-r zz-refl = zz-refl
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l _ rz-rb zz-id-fwd = zz-id-fwd
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l _ rz-rb zz-id-bck = zz-id-bck
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l _ _ zz-comp-fwd = zz-comp-fwd
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l _ _ zz-comp-bck = zz-comp-bck
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l (rz-ra rz> φ) (rz-rb rz> .φ) (zz-cong-fwd p) = zz-cong-fwd (rz•eq-zz rz-l rz-ra rz-rb p)
rz•eq-zz {_}{_} {c} {x}{y}{z} rz-l (rz-ra rz< φ) (rz-rb rz< .φ) (zz-cong-bck p) = zz-cong-bck (rz•eq-zz rz-l rz-ra rz-rb p)

_rz•zz_ : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} → (RawZigzag c x y) → (Zigzag c y z) → (Zigzag c x z)
_rz•zz_ {_}{_} {c} {x}{y}{z0} rz-l zz-r = elim-zz (λ z → Zigzag c x z)
  (λ z rz-r → mk-zz (rz-l rz• rz-r))
  (λ z rz-ra rz-rb p → eq-zz (rz•eq-zz rz-l rz-ra rz-rb p))
  {z0} zz-r

eq-zz•rz : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-la rz-lb : RawZigzag c x y) → (rz-r : RawZigzag c y z)
  → EqZigzag c rz-la rz-lb → (EqZigzag c (rz-la rz• rz-r) (rz-lb rz• rz-r))
eq-zz•rz rz-la rz-lb rz-refl p = p
eq-zz•rz rz-la rz-lb (rz-r rz> φ) p = zz-cong-fwd (eq-zz•rz rz-la rz-lb rz-r p)
eq-zz•rz rz-la rz-lb (rz-r rz< φ) p = zz-cong-bck (eq-zz•rz rz-la rz-lb rz-r p)

eq-zz•zz : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c}
  → (rz-la rz-lb : RawZigzag c x y) → (zz-r : Zigzag c y z)
  → EqZigzag c rz-la rz-lb → ((rz-la rz•zz zz-r) == (rz-lb rz•zz zz-r))
eq-zz•zz {_}{_} {c} {x}{y}{z0} rz-la rz-lb zz-r0 p = elimd-zz {c = c}{x = y}
  (λ z zz-r → (rz-la rz•zz zz-r) == (rz-lb rz•zz zz-r))
  (λ z rz-r → eq-zz (eq-zz•rz rz-la rz-lb rz-r p))
  (λ z rz-ra rz-rb q → uip)
  {z0} zz-r0

_zz•_ : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} → (Zigzag c x y) → (Zigzag c y z) → (Zigzag c x z)
_zz•_ {_}{_} {c} {x}{y0}{z0} zz-l zz-r0 = elim-zz {c = c} {x = x}
  (λ y → (z : c.Obj c) → (Zigzag c y z) → (Zigzag c x z))
  (λ y rz-l z zz-r → rz-l rz•zz zz-r)
  (λ y rz-la rz-lb p → λ= z => λ= zz-r => eq-zz•zz rz-la rz-lb zz-r p)
  {y0} zz-l z0 zz-r0

--associativity of locpath composition------------------

zz•assoc : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {w x y z : c.Obj c}
  → (zz-l : Zigzag c w x) → (zz-m : Zigzag c x y) → (zz-r : Zigzag c y z)
  → (zz-l zz• zz-m) zz• zz-r == zz-l zz• (zz-m zz• zz-r)
zz•assoc {_}{_}{c} {w}{x0}{y0}{z0} zz-l0 zz-m0 zz-r0 =
  elimd-zz
  (λ x zz-l →
    {y z : c.Obj c} → (zz-m : Zigzag c x y) → (zz-r : Zigzag c y z)
    → (zz-l zz• zz-m) zz• zz-r == zz-l zz• (zz-m zz• zz-r)
  )
  (λ x rz-l {y1}{z1} zz-m1 zz-r1 →
    elimd-zz
    (λ y zz-m →
      {z : c.Obj c} → (zz-r : Zigzag c y z)
      → ((mk-zz rz-l) zz• zz-m) zz• zz-r == (mk-zz rz-l) zz• (zz-m zz• zz-r)
    )
    (λ y rz-m {z2} zz-r2 →
      elimd-zz
      (λ z zz-r → ((mk-zz rz-l) zz• (mk-zz rz-m)) zz• zz-r == (mk-zz rz-l) zz• ((mk-zz rz-m) zz• zz-r))
      (λ z rz-r → map= mk-zz (rz•assoc rz-l rz-m rz-r))
      (λ z rz-r rz-r' p → uip)
      {z2} zz-r2
    )
    (λ y rz-m rz-m' p → λ¶i z => λ¶ zz-r => uip)
    {y1} zz-m1 zz-r1
  )
  (λ x rz-l rz-l' p → λ¶i y => λ¶i z => λ¶ zz-m => λ¶ zz-r => uip)
  {x0} zz-l0 zz-m0 zz-r0

--left and right unit laws-------------------------

zz•lunit : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (zz : Zigzag c x y)
  → ((mk-zz rz-refl) zz• zz) == zz
zz•lunit {_}{_}{x} = elimd-zz
  (λ y zz → ((mk-zz rz-refl) zz• zz) == zz)
  (λ y rz → map= mk-zz (rz•lunit rz))
  (λ y rz rz' p → uip)

zz•runit : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (zz : Zigzag c x y)
  → (zz zz• (mk-zz rz-refl)) == zz
zz•runit {_}{_}{x} = elimd-zz
  (λ y zz → (zz zz• (mk-zz rz-refl)) == zz)
  (λ y rz → refl)
  (λ y rz rz' p → uip)
