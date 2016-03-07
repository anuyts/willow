module aken.cat.RawZigzag.Fuse where

open import aken.cat.RawZigzag public
open import aken.cat.Groupoid public

fuseRawZigzag : ∀{ℓo ℓh} → (g : Groupoid ℓo ℓh) → {x y : g.Obj g} → (rz : RawZigzag (g.cat g) x y) → g.Hom g x y
fuseRawZigzag {ℓo}{ℓh} g {x}{.x} rz-refl = g.id g x
fuseRawZigzag {ℓo}{ℓh} g {x}{y} (rz rz> φ) = (g.cat g) $ φ m∘ fuseRawZigzag g rz
fuseRawZigzag {ℓo}{ℓh} g {x}{y} (rz rz< φ) = (g.cat g) $ g.inv g φ m∘ fuseRawZigzag g rz
