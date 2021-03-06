module willow.cat.Locpath.Fuse where

open import willow.cat.Locpath public
open import willow.cat.RawZigzag.Fuse public
open import willow.cat.Groupoid public

--fusing locpaths--------------------------------------

fuseEqLocpath : ∀{ℓo ℓh} → (g : Groupoid ℓo ℓh) → {x y : g.Obj g}
  → (rza rzb : RawZigzag (g.cat g) x y) → (p : EqLocpath (g.cat g) rza rzb) → (fuseRawZigzag g rza == fuseRawZigzag g rzb)
fuseEqLocpath g rzb .rzb lp-refl = refl
fuseEqLocpath g _ rzb lp-id-fwd = g.m∘lunit' g
fuseEqLocpath g _ rzb lp-id-bck = map= (λ φ → g.cat g $ φ m∘ fuseRawZigzag g rzb) (f.hom-id' (g.c-inv g) _) • g.m∘lunit' g
fuseEqLocpath g _ _ lp-comp-fwd = sym (g.m∘assoc' g)
fuseEqLocpath g (rz rz< φ rz< ψ) .(rz rz< (g.cat g $ φ m∘ ψ)) lp-comp-bck =
  g.cat g $ g.inv g ψ m∘ (g.cat g $ g.inv g φ m∘ fuseRawZigzag g rz) == g.cat g $ g.inv g (g.cat g $ φ m∘ ψ) m∘ fuseRawZigzag g rz
  ∋ sym (g.m∘assoc' g) • map= (λ ξ → g.cat g $ ξ m∘ fuseRawZigzag g rz) (sym (f.hom-m∘' (g.c-inv g) ψ φ))
  -- ψ-1 ∘ (φ-1 ∘ rz) = (ψ-1 ∘ φ-1) ∘ rz = (φ ∘ ψ)-1 ∘ rz
fuseEqLocpath g (.rzb rz> φ rz< .φ) rzb lp-cancel-up =
  sym (g.m∘assoc' g) • map= (λ ξ → g.cat g $ ξ m∘ fuseRawZigzag g rzb) (≅.src-id (g.asIso g φ)) • g.m∘lunit' g
  -- φ-1 ∘ (φ ∘ rz) = (φ-1 ∘ φ) ∘ rz = id ∘ rz = rz
fuseEqLocpath g (.rzb rz< φ rz> .φ) rzb lp-cancel-dn =
  sym (g.m∘assoc' g) • map= (λ ξ → g.cat g $ ξ m∘ fuseRawZigzag g rzb) (≅.tgt-id (g.asIso g φ)) • g.m∘lunit' g
fuseEqLocpath g (rza rz> φ) (rzb rz> .φ) (lp-cong-fwd p) = map= (λ ξ → g.cat g $ φ m∘ ξ) (fuseEqLocpath g rza rzb p)
fuseEqLocpath g (rza rz< φ) (rzb rz< .φ) (lp-cong-bck p) = map= (λ ξ → g.cat g $ (g.inv g φ) m∘ ξ) (fuseEqLocpath g rza rzb p)

fuseLocpath : ∀{ℓo ℓh} → (g : Groupoid ℓo ℓh) → {x y : g.Obj g} → (lp : Locpath (g.cat g) x y) → g.Hom g x y
fuseLocpath g {x} = elim-lp
  (λ y → g.Hom g x y)
  (λ y rz → fuseRawZigzag g rz)
  (λ y rz rz' p → fuseEqLocpath g rz rz' p)

fuse-rz•lp : ∀{ℓo ℓh} (g : Groupoid ℓo ℓh) {x y : g.Obj g}
  (rza : RawZigzag (g.cat g) x y) {z : g.Obj g} (lpb : Locpath (g.cat g) y z)
  → (fuseLocpath g (rza rz•lp lpb)) == (g.cat g $ fuseLocpath g lpb m∘ fuseRawZigzag g rza)
fuse-rz•lp g rza = elimd-lp
  (λ z lpb → (fuseLocpath g (rza rz•lp lpb)) == (g.cat g $ fuseLocpath g lpb m∘ fuseRawZigzag g rza))
  (λ y rzb → fuse-rz• g rza rzb)
  (λ y rz rz' p → uip)

fuse-lp• : ∀{ℓo ℓh} (g : Groupoid ℓo ℓh) {x y : g.Obj g}
    (lpa : Locpath (g.cat g) x y) {z : g.Obj g} (lpb : Locpath (g.cat g) y z)
    → (fuseLocpath g (lpa lp• lpb)) == (g.cat g $ fuseLocpath g lpb m∘ fuseLocpath g lpa)
fuse-lp• {ℓo}{ℓh} g {x} = elimd-lp
    (λ y lpa → {z : g.Obj g} (lpb : Locpath (g.cat g) y z)
      → (fuseLocpath g (lpa lp• lpb)) == (g.cat g $ fuseLocpath g lpb m∘ fuseLocpath g lpa))
    (λ y rza lpb → fuse-rz•lp g rza lpb)
    (λ y rz rz' p → λi= z => λ= lpb => uip)

--fuse commutes with functor application-------------------------------

fuse-map-lp : ∀{ℓoA ℓhA ℓoB ℓhB}
  (gA : Groupoid ℓoA ℓhA) (gB : Groupoid ℓoB ℓhB)
  (cf : g.cat gA ++> g.cat gB)
  {x y : g.Obj gA} (lp : Locpath (g.cat gA) x y)
  → f.hom cf (fuseLocpath gA lp) == fuseLocpath gB (mapLocpath cf lp)
fuse-map-lp gA gB cf {x} = elimd-lp
  (λ y lp → f.hom cf (fuseLocpath gA lp) == fuseLocpath gB (mapLocpath cf lp))
  (λ y rz → fuse-map-rz gA gB cf rz)
  (λ y rz rz' p → uip)
