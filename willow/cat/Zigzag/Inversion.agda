module willow.cat.Zigzag.Inversion where

open import willow.cat.RawZigzag public
open import willow.cat.Zigzag.Definition public
open import willow.cat.Zigzag.Tools public
open import willow.cat.Zigzag.Composition public

--inversion of locpaths----------------------------

eq-zz-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rza rzb : RawZigzag c x y) → (p : EqZigzag c rza rzb) → (EqZigzag c (rz-inv rza) (rz-inv rzb))
eq-zz-inv {_}{_} {c} {x}{y} rz .rz zz-refl = zz-refl
eq-zz-inv {_}{_} {c} {x}{y} .(rzb rz> (c.id c y)) rzb zz-id-fwd =
  tra (λ rz-r' → EqZigzag c (rz-inv (rzb rz> (c.id c y))) rz-r') / (rz•lunit (rz-inv rzb)) of
  eq-zz•rz (rz-refl rz< (c.id c y)) rz-refl (rz-inv rzb) zz-id-bck
eq-zz-inv {_}{_} {c} {x}{y} .(rzb rz< (c.id c y)) rzb zz-id-bck =
  tra (λ rz-r' → EqZigzag c (rz-inv (rzb rz< (c.id c y))) rz-r') / (rz•lunit (rz-inv rzb)) of
  eq-zz•rz (rz-refl rz> (c.id c y)) rz-refl (rz-inv rzb) zz-id-fwd
eq-zz-inv {_}{_} {c} {x}{w} (rz rz> φ rz> ψ) .(rz rz> (c $ ψ m∘ φ)) zz-comp-fwd =
  tra (λ rz-l → EqZigzag c rz-l (rz-inv (rz rz> c $ ψ m∘ φ))) / sym (precomp-twice-bck (rz-inv rz) φ ψ) of
  eq-zz•rz (rz-refl rz< ψ rz< φ) (rz-refl rz< (c $ ψ m∘ φ)) (rz-inv rz) zz-comp-bck
eq-zz-inv {_}{_} {c} {x}{y} (rz rz< φ rz< ψ) .(rz rz< (c $ φ m∘ ψ)) zz-comp-bck = 
  tra (λ rz-l → EqZigzag c rz-l (rz-inv (rz rz< c $ φ m∘ ψ))) / sym (precomp-twice-fwd (rz-inv rz) φ ψ) of
  eq-zz•rz (rz-refl rz> ψ rz> φ) (rz-refl rz> (c $ φ m∘ ψ)) (rz-inv rz) zz-comp-fwd
eq-zz-inv {_}{_} {c} {x}{y} (rza rz> φ) (rzb rz> .φ) (zz-cong-fwd p) =
  rz•eq-zz (rz-refl rz< φ) (rz-inv rza) (rz-inv rzb) (eq-zz-inv rza rzb p)
eq-zz-inv {_}{_} {c} {x}{y} (rza rz< φ) (rzb rz< .φ) (zz-cong-bck p) = 
  rz•eq-zz (rz-refl rz> φ) (rz-inv rza) (rz-inv rzb) (eq-zz-inv rza rzb p)

zz-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (Zigzag c x y) → (Zigzag c y x)
zz-inv {_}{_}{c}{x} = elim-zz
  (λ y → Zigzag c y x)
  (λ y rz → mk-zz (rz-inv rz))
  (λ y rza rzb p → eq-zz (eq-zz-inv rza rzb p))

zz-inv-zz• : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (ζ : Zigzag c x y) → {z : c.Obj c} → (η : Zigzag c y z)
  → zz-inv (ζ zz• η) == (zz-inv η) zz• (zz-inv ζ)
zz-inv-zz• {ℓo}{ℓh} {c} {x} = elimd-zz
  (λ y ζ → {z : c.Obj c} → (η : Zigzag c y z) → zz-inv (ζ zz• η) == (zz-inv η) zz• (zz-inv ζ))
  (λ y rz-l → elimd-zz
    (λ z η → zz-inv (mk-zz rz-l zz• η) == (zz-inv η) zz• (zz-inv (mk-zz rz-l)))
    (λ z rz-r → map= mk-zz (rz-inv-rz• rz-l rz-r))
    (λ z rz-r rz-r' p → uip)
  )
  (λ y rz rz' p → λi= z => λ= η => uip)

zz-inv-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c}
  → (ζ : Zigzag c x y) → zz-inv (zz-inv ζ) == ζ
zz-inv-inv {ℓo}{ℓh} {c} {x} = elimd-zz
  (λ y ζ → zz-inv (zz-inv ζ) == ζ)
  (λ y rz → map= mk-zz (rz-inv-inv rz))
  (λ y rz rz' p → uip)
