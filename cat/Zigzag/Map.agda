module willow.cat.Zigzag.Map where

open import willow.cat.RawZigzag public
open import willow.cat.Zigzag.Definition public
open import willow.cat.Zigzag.Composition public
open import willow.cat.Zigzag.Inversion public

--mapping locpaths-----------------------------------------

mapEqZigzag : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (rza rzb : RawZigzag cA x y)
  → (EqZigzag cA rza rzb) → EqZigzag cB (mapRawZigzag cf rza) (mapRawZigzag cf rzb)
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} rzb .rzb zz-refl = zz-refl
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} .(rzb rz> c.id cA y) rzb zz-id-fwd =
  tra (λ φ → EqZigzag cB ((mapRawZigzag cf rzb) rz> φ) (mapRawZigzag cf rzb)) / sym (f.hom-id cf _) of zz-id-fwd
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} .(rzb rz< c.id cA y) rzb zz-id-bck = 
  tra (λ φ → EqZigzag cB ((mapRawZigzag cf rzb) rz< φ) (mapRawZigzag cf rzb)) / sym (f.hom-id cf _) of zz-id-bck
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} (rzb rz> φ rz> ψ) .(rzb rz> cA $ ψ m∘ φ) zz-comp-fwd =
  tra
    (λ ξ → EqZigzag cB
      ((mapRawZigzag cf rzb) rz> (f.hom cf φ) rz> (f.hom cf ψ))
      ((mapRawZigzag cf rzb) rz> ξ)
    )
    / sym (f.hom-m∘ cf _ _) of zz-comp-fwd
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} (rzb rz< φ rz< ψ) .(rzb rz< cA $ φ m∘ ψ) zz-comp-bck = 
  tra
    (λ ξ → EqZigzag cB
      ((mapRawZigzag cf rzb) rz< (f.hom cf φ) rz< (f.hom cf ψ))
      ((mapRawZigzag cf rzb) rz< ξ)
    )
    / sym (f.hom-m∘ cf _ _) of zz-comp-bck
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} _ _ (zz-cong-fwd p) = zz-cong-fwd (mapEqZigzag cf _ _ p)
mapEqZigzag {_}{_}{_}{_} {cA}{cB} cf {x}{y} _ _ (zz-cong-bck p) = zz-cong-bck (mapEqZigzag cf _ _ p)

mapZigzag : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (zz : Zigzag cA x y) → Zigzag cB (f.obj cf x) (f.obj cf y)
mapZigzag cf {x} = elim-zz
  (λ y → Zigzag _ (f.obj cf x) (f.obj cf y))
  (λ y rz → mk-zz (mapRawZigzag cf rz))
  (λ y rz rz' p → eq-zz (mapEqZigzag cf rz rz' p))

map-zz• : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y z : c.Obj cA} → (zz-l : Zigzag cA x y) → (zz-r : Zigzag cA y z)
  → mapZigzag cf (zz-l zz• zz-r) == mapZigzag cf zz-l zz• mapZigzag cf zz-r
map-zz• {_}{_}{_}{_} {cA}{cB} cf {x}{y0}{z0} zz-l0 zz-r0 = elimd-zz
  (λ y zz-l → {z : c.Obj cA} → (zz-r : Zigzag cA y z)
    → mapZigzag cf (zz-l zz• zz-r) == mapZigzag cf zz-l zz• mapZigzag cf zz-r)
  (λ y rz-l {z0} zz-r0 → elimd-zz
    (λ z zz-r → mapZigzag cf (mk-zz rz-l zz• zz-r) == mapZigzag cf (mk-zz rz-l) zz• mapZigzag cf zz-r)
    (λ z rz-r → map= mk-zz (map-rz• cf rz-l rz-r))
    (λ z rz-r rz-r' p → uip)
    {z0} zz-r0
  )
  (λ y rz rz' p → λ¶i z => λ¶ zz-r => uip)
  {y0} zz-l0 {z0} zz-r0

mapZigzag-id : ∀{ℓoA ℓhA} → (c : Cat ℓoA ℓhA) → {x y : c.Obj c} → (zz : Zigzag c x y)
  → mapZigzag (c-id c) zz == zz
mapZigzag-id c {x} = elimd-zz
  (λ y zz → mapZigzag (c-id c) zz == zz)
  (λ y rz → map= mk-zz (mapRawZigzag-id c rz))
  (λ y rz rz' p → uip)

mapZigzag-c∘ : ∀{ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → {cC : Cat ℓoC ℓhC}
  → (cg : cB ++> cC) → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (zz : Zigzag cA x y)
  → mapZigzag (cg c∘ cf) zz == mapZigzag cg (mapZigzag cf zz)
mapZigzag-c∘ cg cf {x} = elimd-zz
  (λ y zz → mapZigzag (cg c∘ cf) zz == mapZigzag cg (mapZigzag cf zz))
  (λ y rz → map= mk-zz (mapRawZigzag-c∘ cg cf rz))
  (λ y rz rz' p → uip)

map-zz-inv : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB)
  → {x y : c.Obj cA} → (ζ : Zigzag cA x y)
  → mapZigzag cf (zz-inv ζ) == zz-inv (mapZigzag cf ζ)
map-zz-inv {_}{_}{_}{_} {cA}{cB} cf {x} = elimd-zz
  (λ y ζ → mapZigzag cf (zz-inv ζ) == zz-inv (mapZigzag cf ζ))
  (λ y rz → map= mk-zz (map-rz-inv cf rz))
  (λ y rz rz' p → uip)
