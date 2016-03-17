module willow.cat.Zigzag.DaggerFuse where

open import willow.cat.Zigzag public
open import willow.cat.RawZigzag.DaggerFuse public
open import willow.cat.DaggerCategory public

--fusing locpaths--------------------------------------

dfuseEqZigzag : ∀{ℓo ℓh} → (dc : DCat ℓo ℓh) → {x y : dc.Obj dc}
  → (rza rzb : RawZigzag (dc.cat dc) x y) → (p : EqZigzag (dc.cat dc) rza rzb) → (dfuseRawZigzag dc rza == dfuseRawZigzag dc rzb)
dfuseEqZigzag dc rzb .rzb zz-refl = refl
dfuseEqZigzag dc _ rzb zz-id-fwd = dc.m∘lunit dc
dfuseEqZigzag dc _ rzb zz-id-bck = map= (λ φ → dc.cat dc $ φ m∘ dfuseRawZigzag dc rzb) (f.hom-id (dc.c† dc) _) • dc.m∘lunit dc
dfuseEqZigzag dc _ _ zz-comp-fwd = sym (dc.m∘assoc dc)
dfuseEqZigzag dc (rz rz< φ rz< ψ) .(rz rz< (dc.cat dc $ φ m∘ ψ)) zz-comp-bck =
  dc.cat dc $ dc.† dc ψ m∘ (dc.cat dc $ dc.† dc φ m∘ dfuseRawZigzag dc rz) == dc.cat dc $ dc.† dc (dc.cat dc $ φ m∘ ψ) m∘ dfuseRawZigzag dc rz
  ∋ sym (dc.m∘assoc dc) • map= (λ ξ → dc.cat dc $ ξ m∘ dfuseRawZigzag dc rz) (sym (f.hom-m∘ (dc.c† dc) φ ψ))
  -- ψ-1 ∘ (φ-1 ∘ rz) = (ψ-1 ∘ φ-1) ∘ rz = (φ ∘ ψ)-1 ∘ rz
dfuseEqZigzag dc (rza rz> φ) (rzb rz> .φ) (zz-cong-fwd p) = map= (λ ξ → dc.cat dc $ φ m∘ ξ) (dfuseEqZigzag dc rza rzb p)
dfuseEqZigzag dc (rza rz< φ) (rzb rz< .φ) (zz-cong-bck p) = map= (λ ξ → dc.cat dc $ (dc.† dc φ) m∘ ξ) (dfuseEqZigzag dc rza rzb p)

dfuseZigzag : ∀{ℓo ℓh} → (dc : DCat ℓo ℓh) → {x y : dc.Obj dc} → (zz : Zigzag (dc.cat dc) x y) → dc.Hom dc x y
dfuseZigzag dc {x} = elim-zz
  (λ y → dc.Hom dc x y)
  (λ y rz → dfuseRawZigzag dc rz)
  (λ y rz rz' p → dfuseEqZigzag dc rz rz' p)

dfuse-rz•zz : ∀{ℓo ℓh} (dc : DCat ℓo ℓh) {x y : dc.Obj dc}
  (rza : RawZigzag (dc.cat dc) x y) {z : dc.Obj dc} (zzb : Zigzag (dc.cat dc) y z)
  → (dfuseZigzag dc (rza rz•zz zzb)) == (dc.cat dc $ dfuseZigzag dc zzb m∘ dfuseRawZigzag dc rza)
dfuse-rz•zz dc rza = elimd-zz
  (λ z zzb → (dfuseZigzag dc (rza rz•zz zzb)) == (dc.cat dc $ dfuseZigzag dc zzb m∘ dfuseRawZigzag dc rza))
  (λ y rzb → dfuse-rz• dc rza rzb)
  (λ y rz rz' p → uip)

dfuse-zz• : ∀{ℓo ℓh} (dc : DCat ℓo ℓh) {x y : dc.Obj dc}
    (zza : Zigzag (dc.cat dc) x y) {z : dc.Obj dc} (zzb : Zigzag (dc.cat dc) y z)
    → (dfuseZigzag dc (zza zz• zzb)) == (dc.cat dc $ dfuseZigzag dc zzb m∘ dfuseZigzag dc zza)
dfuse-zz• {ℓo}{ℓh} dc {x} = elimd-zz
    (λ y zza → {z : dc.Obj dc} (zzb : Zigzag (dc.cat dc) y z)
      → (dfuseZigzag dc (zza zz• zzb)) == (dc.cat dc $ dfuseZigzag dc zzb m∘ dfuseZigzag dc zza))
    (λ y rza zzb → dfuse-rz•zz dc rza zzb)
    (λ y rz rz' p → λi= z => λ= zzb => uip)

--dfuse commutes with functor application-------------------------------

dfuse-map-zz : ∀{ℓoA ℓhA ℓoB ℓhB}
  (dcA : DCat ℓoA ℓhA) (dcB : DCat ℓoB ℓhB)
  (dcf : dcA dc→ dcB)
  {x y : dc.Obj dcA} (zz : Zigzag (dc.cat dcA) x y)
  → df.hom dcf (dfuseZigzag dcA zz) == dfuseZigzag dcB (mapZigzag (df.f dcf) zz)
dfuse-map-zz dcA dcB dcf {x} = elimd-zz
  (λ y zz → df.hom dcf (dfuseZigzag dcA zz) == dfuseZigzag dcB (mapZigzag (df.f dcf) zz))
  (λ y rz → dfuse-map-rz dcA dcB dcf rz)
  (λ y rz rz' p → uip)

--dfuse of the inverse, yields the dagger

dfuse-zz-inv : ∀{ℓo}{ℓh} (dcA : DCat ℓo ℓh) {x y : dc.Obj dcA} (ζ : Zigzag (dc.cat dcA) x y)
  → dfuseZigzag dcA (zz-inv ζ) == dc.† dcA (dfuseZigzag dcA ζ)
dfuse-zz-inv dcA {x} = elimd-zz
  (λ y ζ → dfuseZigzag dcA (zz-inv ζ) == dc.† dcA (dfuseZigzag dcA ζ))
  (λ y rz → dfuse-rz-inv dcA rz)
  (λ y rz rz' p → uip)
