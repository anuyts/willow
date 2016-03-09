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
