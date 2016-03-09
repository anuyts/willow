module willow.cat.RawZigzag.Fuse where

open import willow.cat.RawZigzag public
open import willow.cat.Groupoid public

fuseRawZigzag : ∀{ℓo ℓh} → (g : Groupoid ℓo ℓh) → {x y : g.Obj g} → (rz : RawZigzag (g.cat g) x y) → g.Hom g x y
fuseRawZigzag {ℓo}{ℓh} g {x}{.x} rz-refl = g.id g x
fuseRawZigzag {ℓo}{ℓh} g {x}{y} (rz rz> φ) = (g.cat g) $ φ m∘ fuseRawZigzag g rz
fuseRawZigzag {ℓo}{ℓh} g {x}{y} (rz rz< φ) = (g.cat g) $ g.inv g φ m∘ fuseRawZigzag g rz

fuse-rz• : ∀{ℓo ℓh} (g : Groupoid ℓo ℓh) {x y z : g.Obj g}
  (rza : RawZigzag (g.cat g) x y) (rzb : RawZigzag (g.cat g) y z)
  → (fuseRawZigzag g (rza rz• rzb)) == (g.cat g $ fuseRawZigzag g rzb m∘ fuseRawZigzag g rza)
fuse-rz• g rza rz-refl = sym (g.m∘lunit g)
fuse-rz• g rza (rzb rz> φ) =
  {- fuse(rza • (rzb, φ))
  := fuse(rza • rzb, φ)
  := φ ∘ fuse(rza • rzb)
   = φ ∘ (fuse(rzb) ∘ fuse(rza))
   = (φ ∘ fuse(rzb)) ∘ fuse(rza)
   =: fuse(rzb, φ) ∘ fuse(rza)
  -}
  via (g.cat g $ φ m∘ fuseRawZigzag g (rza rz• rzb)) $ refl •
  via (g.cat g $ φ m∘ (g.cat g $ fuseRawZigzag g rzb m∘ fuseRawZigzag g rza)) $
    map= (λ ξ → g.cat g $ φ m∘ ξ) (fuse-rz• g rza rzb) •
  via (g.cat g $ (g.cat g $ φ m∘ fuseRawZigzag g rzb) m∘ fuseRawZigzag g rza) $ sym (g.m∘assoc g) •
  refl
fuse-rz• g rza (rzb rz< φ) =
  via (g.cat g $ g.inv g φ m∘ fuseRawZigzag g (rza rz• rzb)) $ refl •
  via (g.cat g $ g.inv g φ m∘ (g.cat g $ fuseRawZigzag g rzb m∘ fuseRawZigzag g rza)) $
    map= (λ ξ → g.cat g $ g.inv g φ m∘ ξ) (fuse-rz• g rza rzb) •
  via (g.cat g $ (g.cat g $ g.inv g φ m∘ fuseRawZigzag g rzb) m∘ fuseRawZigzag g rza) $ sym (g.m∘assoc g) •
  refl

--fuse commutes with functor application-------------------------------

fuse-map-rz : ∀{ℓoA ℓhA ℓoB ℓhB}
  (gA : Groupoid ℓoA ℓhA) (gB : Groupoid ℓoB ℓhB)
  (cf : g.cat gA ++> g.cat gB)
  {x y : g.Obj gA} (rz : RawZigzag (g.cat gA) x y)
  → f.hom cf (fuseRawZigzag gA rz) == fuseRawZigzag gB (mapRawZigzag cf rz)
fuse-map-rz gA gB cf rz-refl = f.hom-id cf _
fuse-map-rz gA gB cf (rz rz> φ) =
  --f(fuse(rz, φ)) := f(φ ∘ fuse(rz)) = f(φ) ∘ f(fuse(rz)) = f(φ) ∘ fuse(f(rz)) =: fuse(f(rz), f(φ)) =: fuse(f(rz, φ))
  via f.hom cf (fuseRawZigzag gA (rz rz> φ)) $ refl •
  via f.hom cf (g.cat gA $ φ m∘ fuseRawZigzag gA rz) $ refl •
  via (g.cat gB $ f.hom cf φ m∘ f.hom cf (fuseRawZigzag gA rz)) $ f.hom-m∘ cf φ (fuseRawZigzag gA rz) •
  via (g.cat gB $ f.hom cf φ m∘ fuseRawZigzag gB (mapRawZigzag cf rz)) $
    map= (λ ξ → g.cat gB $ f.hom cf φ m∘ ξ) (fuse-map-rz gA gB cf rz) • 
  refl
fuse-map-rz gA gB cf (rz rz< φ) =
  --f(fuse(rz, φ*)) := f(φ-1 ∘ fuse(rz)) = f(φ-1) ∘ f(fuse(rz)) = f(φ)-1 ∘ f(fuse(rz)) = f(φ)-1 ∘ fuse(f(rz)) =: fuse(f(rz, φ*))
  via f.hom cf (fuseRawZigzag gA (rz rz< φ)) $ refl •
  via f.hom cf (g.cat gA $ g.inv gA φ m∘ fuseRawZigzag gA rz) $ refl •
  via (g.cat gB $ f.hom cf (g.inv gA φ) m∘ f.hom cf (fuseRawZigzag gA rz)) $ f.hom-m∘ cf (g.inv gA φ) (fuseRawZigzag gA rz) •
  via (g.cat gB $ g.inv gB (f.hom cf φ) m∘ f.hom cf (fuseRawZigzag gA rz)) $
    map= (λ ξ → g.cat gB $ ξ m∘ f.hom cf (fuseRawZigzag gA rz)) (f-hom-inv gA gB cf φ) •
  via (g.cat gB $ g.inv gB (f.hom cf φ) m∘ fuseRawZigzag gB (mapRawZigzag cf rz)) $
    map= (λ ξ → g.cat gB $ g.inv gB (f.hom cf φ) m∘ ξ) (fuse-map-rz gA gB cf rz) • 
  refl

--the adjunction lemma-----------------------------------------------

{-
adjunction-lemma : ∀{ℓoA ℓhA ℓoB ℓhB}
  (cA : Cat ℓoA ℓhA) (gB : Groupoid ℓoB ℓhB)
  (cf : cLoc cA ++> g.cat gB)
  {x y : c.Obj cA} (rz : RawZigzag cA x y)
-}
