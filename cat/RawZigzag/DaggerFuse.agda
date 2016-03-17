module willow.cat.RawZigzag.DaggerFuse where

open import willow.cat.RawZigzag public
open import willow.cat.DaggerCategory public

dfuseRawZigzag : ∀{ℓo ℓh} → (dc : DCat ℓo ℓh) → {x y : dc.Obj dc} → (rz : RawZigzag (dc.cat dc) x y) → dc.Hom dc x y
dfuseRawZigzag {ℓo}{ℓh} dc {x}{.x} rz-refl = dc.id dc x
dfuseRawZigzag {ℓo}{ℓh} dc {x}{y} (rz rz> φ) = (dc.cat dc) $ φ m∘ dfuseRawZigzag dc rz
dfuseRawZigzag {ℓo}{ℓh} dc {x}{y} (rz rz< φ) = (dc.cat dc) $ dc.† dc φ m∘ dfuseRawZigzag dc rz

dfuse-rz• : ∀{ℓo ℓh} (dc : DCat ℓo ℓh) {x y z : dc.Obj dc}
  (rza : RawZigzag (dc.cat dc) x y) (rzb : RawZigzag (dc.cat dc) y z)
  → (dfuseRawZigzag dc (rza rz• rzb)) == (dc.cat dc $ dfuseRawZigzag dc rzb m∘ dfuseRawZigzag dc rza)
dfuse-rz• dc rza rz-refl = sym (dc.m∘lunit dc)
dfuse-rz• dc rza (rzb rz> φ) =
  {- dfuse(rza • (rzb, φ))
  := dfuse(rza • rzb, φ)
  := φ ∘ dfuse(rza • rzb)
   = φ ∘ (dfuse(rzb) ∘ dfuse(rza))
   = (φ ∘ dfuse(rzb)) ∘ dfuse(rza)
   =: dfuse(rzb, φ) ∘ dfuse(rza)
  -}
  via (dc.cat dc $ φ m∘ dfuseRawZigzag dc (rza rz• rzb)) $ refl •
  via (dc.cat dc $ φ m∘ (dc.cat dc $ dfuseRawZigzag dc rzb m∘ dfuseRawZigzag dc rza)) $
    map= (λ ξ → dc.cat dc $ φ m∘ ξ) (dfuse-rz• dc rza rzb) •
  via (dc.cat dc $ (dc.cat dc $ φ m∘ dfuseRawZigzag dc rzb) m∘ dfuseRawZigzag dc rza) $ sym (dc.m∘assoc dc) •
  refl
dfuse-rz• dc rza (rzb rz< φ) =
  via (dc.cat dc $ dc.† dc φ m∘ dfuseRawZigzag dc (rza rz• rzb)) $ refl •
  via (dc.cat dc $ dc.† dc φ m∘ (dc.cat dc $ dfuseRawZigzag dc rzb m∘ dfuseRawZigzag dc rza)) $
    map= (λ ξ → dc.cat dc $ dc.† dc φ m∘ ξ) (dfuse-rz• dc rza rzb) •
  via (dc.cat dc $ (dc.cat dc $ dc.† dc φ m∘ dfuseRawZigzag dc rzb) m∘ dfuseRawZigzag dc rza) $ sym (dc.m∘assoc dc) •
  refl

--dfuse commutes with functor application-------------------------------

dfuse-map-rz : ∀{ℓoA ℓhA ℓoB ℓhB}
  (dcA : DCat ℓoA ℓhA) (dcB : DCat ℓoB ℓhB)
  (dcf : dcA dc→ dcB)
  {x y : dc.Obj dcA} (rz : RawZigzag (dc.cat dcA) x y)
  → df.hom dcf (dfuseRawZigzag dcA rz) == dfuseRawZigzag dcB (mapRawZigzag (df.f dcf) rz)
dfuse-map-rz dcA dcB dcf rz-refl = df.hom-id dcf _
dfuse-map-rz dcA dcB dcf (rz rz> φ) =
  --f(dfuse(rz, φ)) := f(φ ∘ dfuse(rz)) = f(φ) ∘ f(dfuse(rz)) = f(φ) ∘ dfuse(f(rz)) =: dfuse(f(rz), f(φ)) =: dfuse(f(rz, φ))
  via df.hom dcf (dfuseRawZigzag dcA (rz rz> φ)) $ refl •
  via df.hom dcf (dc.cat dcA $ φ m∘ dfuseRawZigzag dcA rz) $ refl •
  via (dc.cat dcB $ df.hom dcf φ m∘ df.hom dcf (dfuseRawZigzag dcA rz)) $ df.hom-m∘ dcf φ (dfuseRawZigzag dcA rz) •
  via (dc.cat dcB $ df.hom dcf φ m∘ dfuseRawZigzag dcB (mapRawZigzag (df.f dcf) rz)) $
    map= (λ ξ → dc.cat dcB $ df.hom dcf φ m∘ ξ) (dfuse-map-rz dcA dcB dcf rz) • 
  refl
dfuse-map-rz dcA dcB dcf (rz rz< φ) =
  --f(dfuse(rz, φ*)) := f(φ-1 ∘ dfuse(rz)) = f(φ-1) ∘ f(dfuse(rz)) = f(φ)-1 ∘ f(dfuse(rz)) = f(φ)-1 ∘ dfuse(f(rz)) =: dfuse(f(rz, φ*))
  via df.hom dcf (dfuseRawZigzag dcA (rz rz< φ)) $ refl •
  via df.hom dcf (dc.cat dcA $ dc.† dcA φ m∘ dfuseRawZigzag dcA rz) $ refl •
  via (dc.cat dcB $ df.hom dcf (dc.† dcA φ) m∘ df.hom dcf (dfuseRawZigzag dcA rz)) $ df.hom-m∘ dcf (dc.† dcA φ) (dfuseRawZigzag dcA rz) •
  via (dc.cat dcB $ dc.† dcB (df.hom dcf φ) m∘ df.hom dcf (dfuseRawZigzag dcA rz)) $
    map= (λ ξ → dc.cat dcB $ ξ m∘ df.hom dcf (dfuseRawZigzag dcA rz)) (df.hom-† dcf φ) •
  via (dc.cat dcB $ dc.† dcB (df.hom dcf φ) m∘ dfuseRawZigzag dcB (mapRawZigzag (df.f dcf) rz)) $
    map= (λ ξ → dc.cat dcB $ dc.† dcB (df.hom dcf φ) m∘ ξ) (dfuse-map-rz dcA dcB dcf rz) • 
  refl

--dfuse of the inverse, yields the dagger

dfuse-rz-inv : ∀{ℓo}{ℓh} (dcA : DCat ℓo ℓh) {x y : dc.Obj dcA} (rz : RawZigzag (dc.cat dcA) x y)
  → dfuseRawZigzag dcA (rz-inv rz) == dc.† dcA (dfuseRawZigzag dcA rz)
dfuse-rz-inv dcA rz-refl = sym (dc.†-id dcA _)
dfuse-rz-inv dcA (rz rz> φ) =
  dfuse-rz• dcA (rz-bck φ) (rz-inv rz) •
  map= (λ ξ → (dc.cat dcA) $ (dfuseRawZigzag dcA (rz-inv rz)) m∘ ξ) (dc.m∘runit dcA) •
  map= (λ ξ → (dc.cat dcA) $ ξ m∘ dc.† dcA φ) (dfuse-rz-inv dcA rz) •
  sym (dc.†-m∘ dcA φ (dfuseRawZigzag dcA rz))
dfuse-rz-inv dcA (rz rz< φ) = 
  dfuse-rz• dcA (rz-fwd φ) (rz-inv rz) •
  map= (λ ξ → (dc.cat dcA) $ (dfuseRawZigzag dcA (rz-inv rz)) m∘ ξ) (dc.m∘runit dcA) •
  map= (λ ξ → (dc.cat dcA) $ (dfuseRawZigzag dcA (rz-inv rz)) m∘ ξ) (sym (dc.††-eq dcA φ)) •
  map= (λ ξ → (dc.cat dcA) $ ξ m∘ dc.† dcA (dc.† dcA φ)) (dfuse-rz-inv dcA rz) •
  sym (dc.†-m∘ dcA (dc.† dcA φ) (dfuseRawZigzag dcA rz))
