module willow.cat.Locpath.Map where

open import willow.cat.RawZigzag public
open import willow.cat.Locpath.Definition public
open import willow.cat.Locpath.Composition public

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
