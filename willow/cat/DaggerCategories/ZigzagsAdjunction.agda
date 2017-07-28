module willow.cat.DaggerCategories.ZigzagsAdjunction where

open import willow.cat.DaggerCategories.ZigzagsFunctor public
open import willow.cat.Adjunction public

-- prerequisites ----------------------------

zigzagsAdjunction:fwd:obj : ∀{ℓo ℓh}
  (cL,dcR : Cat ℓo (ℓo ⊔ ℓh) × DCat ℓo (ℓo ⊔ ℓh))
  (dcf : dcZigzags (prl cL,dcR) dc→ prr cL,dcR)
  → prl cL,dcR ++> dc.cat (prr cL,dcR)
zigzagsAdjunction:fwd:obj cL,dcR dcf = record
    { obj = df.obj dcf
    ; hom = λ φ → df.hom dcf (zz-fwd φ)
    ; hom-id =
      -- f((id)) = f(()) = id
      λ x → map= (df.hom dcf) (eq-zz zz-id-fwd) • df.hom-id' dcf x
    ; hom-m∘ =
      -- f((ψ ∘ φ)) = f((φ, ψ)) = f((φ) • (ψ)) = f((ψ)) ∘ f((φ))
      λ ψ φ →
        via df.hom dcf (zz-fwd (prl cL,dcR $ ψ m∘ φ)) $ refl •
        via df.hom dcf (zz-nil zz> φ zz> ψ) $ map= (df.hom dcf) (sym (eq-zz zz-comp-fwd)) •
        via df.hom dcf ((zz-fwd φ) zz• (zz-fwd ψ)) $ refl •
        via (dc.cat (prr cL,dcR) $ df.hom dcf (zz-fwd ψ) m∘ df.hom dcf (zz-fwd φ)) $ df.hom-m∘' dcf (zz-fwd ψ) (zz-fwd φ) •
        refl
    }

zigzagsAdjunction:lemma : ∀{ℓo ℓh}
  (cL,dcR : Cat ℓo (ℓo ⊔ ℓh) × DCat ℓo (ℓo ⊔ ℓh))
  (dcf : dcZigzags (prl cL,dcR) dc→ prr cL,dcR)
  (x y : c.Obj (prl cL,dcR)) (rz : RawZigzag (prl cL,dcR) x y)
  → dfuseZigzag
       (prr cL,dcR)
       (mapZigzag (zigzagsAdjunction:fwd:obj{ℓo}{ℓh} cL,dcR dcf) (mk-zz rz))
     == df.hom dcf (mk-zz rz)
zigzagsAdjunction:lemma {ℓo}{ℓh} cL,dcR dcf x .x rz-refl = sym (df.hom-id' dcf x)
-- f>< (mkzz (rz, φ)) := dfuse[ (loc f>)(rz, φ) ] := dfuse((loc f>)(rz), (f>)(φ)) := dfuse( (loc f>)(rz), f((φ)) )
-- := f((φ)) ∘ dfuse[ (loc f>)(rz) ] =: f((φ)) ∘ f>< (mkzz rz) = f((φ)) ∘ f(mkzz rz) = f((φ) ∘ mkzz rz)
-- := f(mkzz rz • (φ)) := f(mkzz (rz, φ))
zigzagsAdjunction:lemma {ℓo}{ℓh} cL,dcR dcf x z (rz rz> φ) =
  via (
    dc.cat (prr cL,dcR) $
    df.hom dcf (zz-fwd φ) m∘
    dfuseZigzag
      (prr cL,dcR)
      (mapZigzag (zigzagsAdjunction:fwd:obj{ℓo}{ℓh} cL,dcR dcf) (mk-zz rz))
  ) $ refl •
  via (dc.cat (prr cL,dcR) $ df.hom dcf (zz-fwd φ) m∘ df.hom dcf (mk-zz rz)) $
    map= (λ ξ → dc.cat (prr cL,dcR) $ df.hom dcf (zz-fwd φ) m∘ ξ) (zigzagsAdjunction:lemma {ℓo}{ℓh} cL,dcR dcf x _ rz) •
  via df.hom dcf (cZigzags(prl cL,dcR) $ zz-fwd φ m∘ mk-zz rz) $ sym (df.hom-m∘' dcf (zz-fwd φ) (mk-zz rz)) •
  refl
-- f>< (mkzz (rz, φ*)) := dfuse[ (loc f>)(rz, φ*) ] := dfuse((loc f>)(rz), (f>)(φ)*) := dfuse( (loc f>)(rz), f((φ))* )
-- := f((φ))-1 ∘ dfuse[ (loc f>)(rz) ] =: f((φ))-1 ∘ f>< (mkzz rz) = f((φ))-1 ∘ f(mkzz rz) = f((φ)-1) ∘ f(mkzz rz)
-- := f((φ*)) ∘ f(mkzz rz) = f((φ*) ∘ mkzz rz)
-- := f(mkzz rz • (φ*)) := f(mkzz (rz, φ*))
zigzagsAdjunction:lemma {ℓo}{ℓh} cL,dcR dcf x z (rz rz< φ) = 
  via (
    dc.cat (prr cL,dcR) $
    dc.† (prr cL,dcR) (df.hom dcf (zz-fwd φ)) m∘
    dfuseZigzag
      (prr cL,dcR)
      (mapZigzag (zigzagsAdjunction:fwd:obj{ℓo}{ℓh} cL,dcR dcf) (mk-zz rz))
  ) $ refl •
  via (dc.cat (prr cL,dcR) $ dc.† (prr cL,dcR) (df.hom dcf (zz-fwd φ)) m∘ df.hom dcf (mk-zz rz)) $
    map=
      (λ ξ → dc.cat (prr cL,dcR) $ dc.† (prr cL,dcR) (df.hom dcf (zz-fwd φ)) m∘ ξ)
      (zigzagsAdjunction:lemma {ℓo}{ℓh} cL,dcR dcf x _ rz) •
  via (dc.cat (prr cL,dcR) $ df.hom dcf (dc.† (dcZigzags (prl cL,dcR)) (zz-fwd φ)) m∘ df.hom dcf (mk-zz rz)) $
    map=
      (λ ξ → dc.cat (prr cL,dcR) $ ξ m∘ df.hom dcf (mk-zz rz))
      (sym (df.hom-† dcf (zz-fwd φ))) •
  via (dc.cat (prr cL,dcR) $ df.hom dcf (zz-bck φ) m∘ df.hom dcf (mk-zz rz)) $ refl •
  via df.hom dcf (cZigzags(prl cL,dcR) $ zz-bck φ m∘ mk-zz rz) $ sym (df.hom-m∘' dcf (zz-bck φ) (mk-zz rz)) •
  refl

-- the adjunction ----------------------

zigzagsAdjunction : ∀{ℓo ℓh} → czigzags{ℓo}{ℓo ⊔ ℓh} ⊣ cforgetDagger{ℓo}{ℓo ⊔ ℓh}

-- dcf : zigzags cL → dcR. Make cf : cL → fget dcR
_nt→_.obj (Iso.fwd (zigzagsAdjunction{ℓo}{ℓh})) = zigzagsAdjunction:fwd:obj{ℓo}{ℓh}

-- cg : L' → L, dcf : zigzags L → R, dch : R → R' ; now show that (fget ch) ∘ cf> ∘ cg = (dch ∘ dcf ∘ (zigzag cg))>
_nt→_.hom (Iso.fwd zigzagsAdjunction) cg,dch = λ= dcf => functorext (pair-ext refl refl)


-- cf : cL → fget dcR. Make dcf< : zigzags cL → cR
_++>_.obj (_dc→_.f (_nt→_.obj (Iso.bck zigzagsAdjunction) cL,dcR cf)) = f.obj cf
_++>_.hom (_dc→_.f (_nt→_.obj (Iso.bck zigzagsAdjunction) cL,dcR cf)) ζ = dfuseZigzag (prr cL,dcR) (mapZigzag cf ζ)
_++>_.hom-id' (_dc→_.f (_nt→_.obj (Iso.bck zigzagsAdjunction) cL,dcR cf)) x = refl
_++>_.hom-m∘' (_dc→_.f (_nt→_.obj (Iso.bck zigzagsAdjunction) cL,dcR cf)) η ζ =
-- (f<)(zza • zzb) := dfuse(f(zza • zzb)) = dfuse(f(zza) • f(zzb)) = dfuse(f(zzb)) ∘ dfuse(f(zza)) =: (f<)(zzb) ∘ (f<)(zza)
      via dfuseZigzag (prr cL,dcR) (mapZigzag cf (ζ zz• η)) $ refl •
      via dfuseZigzag (prr cL,dcR) (mapZigzag cf ζ zz• mapZigzag cf η) $
        map= (dfuseZigzag (prr cL,dcR)) (map-zz• cf ζ η) •
      via (
        dc.cat (prr cL,dcR) $
        dfuseZigzag (prr cL,dcR) (mapZigzag cf η) m∘
        dfuseZigzag (prr cL,dcR) (mapZigzag cf ζ)
      ) $ dfuse-zz• (prr cL,dcR) (mapZigzag cf ζ) (mapZigzag cf η) •
      refl
_dc→_.hom-† (_nt→_.obj (Iso.bck zigzagsAdjunction) cL,dcR cf) ζ =
  map= (dfuseZigzag (prr cL,dcR)) (map-zz-inv cf ζ) •
  dfuse-zz-inv (prr cL,dcR) (mapZigzag cf ζ)


-- cg : L' → L, cf : L → fget R, dch : R → R' ; now show that dch ∘ dcf< ∘ (zigzag cg) = ((fget dch) ∘ cf ∘ cg)
_nt→_.hom (Iso.bck zigzagsAdjunction) {cL,dcR}{cL,dcR'} cg,dch = λ= cf => dfunctorext (functorext (pair-ext refl (
  λi= x => λi= y => λ= zz =>
    via df.hom (prr cg,dch) (dfuseZigzag (prr cL,dcR) (mapZigzag cf (mapZigzag (prl cg,dch) zz))) $
          refl •
    via dfuseZigzag (prr cL,dcR') (mapZigzag (df.f (prr cg,dch)) (mapZigzag cf (mapZigzag (prl cg,dch) zz))) $
          dfuse-map-zz (prr cL,dcR) (prr cL,dcR') (prr cg,dch) (mapZigzag cf (mapZigzag (prl cg,dch) zz)) •
    via dfuseZigzag (prr cL,dcR') (mapZigzag (df.f (prr cg,dch) c∘ cf) (mapZigzag (prl cg,dch) zz)) $
          map=
            (dfuseZigzag (prr cL,dcR'))
            (sym (mapZigzag-c∘ (df.f (prr cg,dch)) cf (mapZigzag (prl cg,dch) zz)))
          •
    via dfuseZigzag (prr cL,dcR') (mapZigzag (df.f(prr cg,dch) c∘ cf c∘ prl cg,dch) zz) $
          map=
            (λ zz' → dfuseZigzag (prr cL,dcR') zz')
            (sym (mapZigzag-c∘ (df.f(prr cg,dch) c∘ cf) (prl cg,dch) zz))
          •
    refl
  )))


Iso.src-id (zigzagsAdjunction{ℓo}{ℓh}) =
  nt-ext (λ= cL,dcR => λ= dcf => dfunctorext (functorext (pair-ext refl (
    λi= x => λi= y0 => λ= zz0 => elimd-zz
      (λ y zz →
          dfuseZigzag (prr cL,dcR) (mapZigzag (nt.obj(≅.fwd (zigzagsAdjunction{ℓo}{ℓh})) cL,dcR dcf) zz) == df.hom dcf zz)
      (zigzagsAdjunction:lemma {ℓo}{ℓh} cL,dcR dcf x)
      (λ y rz rz' p → uip)
      zz0
  ))))


Iso.tgt-id zigzagsAdjunction = nt-ext (λ= cL,dcR => λ= cf => functorext (pair-ext
    refl
    (λi= x => λi= y => λ= φ => dc.m∘runit' (prr cL,dcR))
  ))
