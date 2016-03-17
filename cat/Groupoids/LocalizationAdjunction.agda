module willow.cat.Groupoids.LocalizationAdjunction where

open import willow.cat.Groupoids.LocalizationFunctor public
open import willow.cat.Adjunction public

-- prerequisites --------------------

localizationAdjunction:fwd:obj : ∀{ℓo ℓh}
  (cL,gR : Cat ℓo (ℓo ⊔ ℓh) × Groupoid ℓo (ℓo ⊔ ℓh))
  (cf : cLoc (prl cL,gR) ++> g.cat (prr cL,gR))
  → prl cL,gR ++> g.cat (prr cL,gR)
localizationAdjunction:fwd:obj cL,gR cf = record
    { obj = f.obj cf
    ; hom = λ φ → f.hom cf (lp-fwd φ)
    ; hom-id =
      -- f((id)) = f(()) = id
      λ x → map= (f.hom cf) (eq-lp lp-id-fwd) • f.hom-id cf x
    ; hom-m∘ =
      -- f((ψ ∘ φ)) = f((φ, ψ)) = f((φ) • (ψ)) = f((ψ)) ∘ f((φ))
      λ ψ φ →
        via f.hom cf (lp-fwd (prl cL,gR $ ψ m∘ φ)) $ refl •
        via f.hom cf (lp-nil lp> φ lp> ψ) $ map= (f.hom cf) (sym (eq-lp lp-comp-fwd)) •
        via f.hom cf ((lp-fwd φ) lp• (lp-fwd ψ)) $ refl •
        via (g.cat (prr cL,gR) $ f.hom cf (lp-fwd ψ) m∘ f.hom cf (lp-fwd φ)) $ f.hom-m∘ cf (lp-fwd ψ) (lp-fwd φ) •
        refl
    }

localizationAdjunction:lemma : ∀{ℓo ℓh}
  (cL,gR : Cat ℓo (ℓo ⊔ ℓh) × Groupoid ℓo (ℓo ⊔ ℓh))
  (cf : cLoc (prl cL,gR) ++> g.cat (prr cL,gR))
  (x y : c.Obj (prl cL,gR)) (rz : RawZigzag (prl cL,gR) x y)
  → fuseLocpath
       (prr cL,gR)
       (mapLocpath (localizationAdjunction:fwd:obj{ℓo}{ℓh} cL,gR cf) (mk-lp rz))
     == f.hom cf (mk-lp rz)
localizationAdjunction:lemma {ℓo}{ℓh} cL,gR cf x .x rz-refl = sym (f.hom-id cf x)
-- f>< (mklp (rz, φ)) := fuse[ (loc f>)(rz, φ) ] := fuse((loc f>)(rz), (f>)(φ)) := fuse( (loc f>)(rz), f((φ)) )
-- := f((φ)) ∘ fuse[ (loc f>)(rz) ] =: f((φ)) ∘ f>< (mklp rz) = f((φ)) ∘ f(mklp rz) = f((φ) ∘ mklp rz)
-- := f(mklp rz • (φ)) := f(mklp (rz, φ))
localizationAdjunction:lemma {ℓo}{ℓh} cL,gR cf x z (rz rz> φ) =
  via (
    g.cat (prr cL,gR) $
    f.hom cf (lp-fwd φ) m∘
    fuseLocpath
      (prr cL,gR)
      (mapLocpath (localizationAdjunction:fwd:obj{ℓo}{ℓh} cL,gR cf) (mk-lp rz))
  ) $ refl •
  via (g.cat (prr cL,gR) $ f.hom cf (lp-fwd φ) m∘ f.hom cf (mk-lp rz)) $
    map= (λ ξ → g.cat (prr cL,gR) $ f.hom cf (lp-fwd φ) m∘ ξ) (localizationAdjunction:lemma {ℓo}{ℓh} cL,gR cf x _ rz) •
  via f.hom cf (cLoc(prl cL,gR) $ lp-fwd φ m∘ mk-lp rz) $ sym (f.hom-m∘ cf (lp-fwd φ) (mk-lp rz)) •
  refl
-- f>< (mklp (rz, φ*)) := fuse[ (loc f>)(rz, φ*) ] := fuse((loc f>)(rz), (f>)(φ)*) := fuse( (loc f>)(rz), f((φ))* )
-- := f((φ))-1 ∘ fuse[ (loc f>)(rz) ] =: f((φ))-1 ∘ f>< (mklp rz) = f((φ))-1 ∘ f(mklp rz) = f((φ)-1) ∘ f(mklp rz)
-- := f((φ*)) ∘ f(mklp rz) = f((φ*) ∘ mklp rz)
-- := f(mklp rz • (φ*)) := f(mklp (rz, φ*))
localizationAdjunction:lemma {ℓo}{ℓh} cL,gR cf x z (rz rz< φ) = 
  via (
    g.cat (prr cL,gR) $
    g.inv (prr cL,gR) (f.hom cf (lp-fwd φ)) m∘
    fuseLocpath
      (prr cL,gR)
      (mapLocpath (localizationAdjunction:fwd:obj{ℓo}{ℓh} cL,gR cf) (mk-lp rz))
  ) $ refl •
  via (g.cat (prr cL,gR) $ g.inv (prr cL,gR) (f.hom cf (lp-fwd φ)) m∘ f.hom cf (mk-lp rz)) $
    map=
      (λ ξ → g.cat (prr cL,gR) $ g.inv (prr cL,gR) (f.hom cf (lp-fwd φ)) m∘ ξ)
      (localizationAdjunction:lemma {ℓo}{ℓh} cL,gR cf x _ rz) •
  via (g.cat (prr cL,gR) $ f.hom cf (g.inv (gLoc (prl cL,gR)) (lp-fwd φ)) m∘ f.hom cf (mk-lp rz)) $
    map=
      (λ ξ → g.cat (prr cL,gR) $ ξ m∘ f.hom cf (mk-lp rz))
      (sym (f-hom-inv (gLoc (prl cL,gR)) (prr cL,gR) cf (lp-fwd φ))) •
  via (g.cat (prr cL,gR) $ f.hom cf (lp-bck φ) m∘ f.hom cf (mk-lp rz)) $ refl •
  via f.hom cf (cLoc(prl cL,gR) $ lp-bck φ m∘ mk-lp rz) $ sym (f.hom-m∘ cf (lp-bck φ) (mk-lp rz)) •
  refl

-- the adjunction ----------------------

localizationAdjunction : ∀{ℓo ℓh} → cloc{ℓo}{ℓo ⊔ ℓh} ⊣ cforgetGrpd{ℓo}{ℓo ⊔ ℓh}

-- cf : loc L → R ; now create functor cf> : L → R
nt.obj (≅.fwd (localizationAdjunction{ℓo}{ℓh})) = localizationAdjunction:fwd:obj{ℓo}{ℓh}
    
-- cg : L' → L , ch : R → R' ; now show that ch ∘ cf> ∘ cg = (ch ∘ cf> ∘ (loc cg))
nt.hom (≅.fwd localizationAdjunction) {cL,gR}{cL,gR'} cg,ch = λ= cf => functorext (pair-ext refl refl)

-- cf : L → R ; now create functor cf< : loc L → R
nt.obj (≅.bck localizationAdjunction) cL,gR cf = record
    { obj = f.obj cf
    ; hom = λ lp → fuseLocpath (prr cL,gR) (mapLocpath cf lp)
    ; hom-id = λ x → refl
    ; hom-m∘ =
      -- (f<)(lpa • lpb) := fuse(f(lpa • lpb)) = fuse(f(lpa) • f(lpb)) = fuse(f(lpb)) ∘ fuse(f(lpa)) =: (f<)(lpb) ∘ (f<)(lpa)
      λ lpb lpa →
      via fuseLocpath (prr cL,gR) (mapLocpath cf (lpa lp• lpb)) $ refl •
      via fuseLocpath (prr cL,gR) (mapLocpath cf lpa lp• mapLocpath cf lpb) $
        map= (fuseLocpath (prr cL,gR)) (map-lp• cf lpa lpb) •
      via (g.cat (prr cL,gR) $ fuseLocpath (prr cL,gR) (mapLocpath cf lpb) m∘ fuseLocpath (prr cL,gR) (mapLocpath cf lpa)) $
        fuse-lp• (prr cL,gR) (mapLocpath cf lpa) (mapLocpath cf lpb) •
      refl
    }
    
-- cg : L' → L , ch : R → R' ; now show that ch ∘ cf< ∘ (loc cg) = (ch ∘ cf ∘ cg)<
nt.hom (≅.bck localizationAdjunction) {cL,gR}{cL,gR'} cg,ch =
    -- f.hom LHS = ch ∘ fuse ∘ (loc cf) ∘ (loc cg).
    -- f.hom RHS = fuse ∘ (loc (ch ∘ cf ∘ cg))
    λ= cf => functorext (pair-ext refl (λi= x => λi= y => λ= lp =>
        {- (ch ∘ fuse ∘ (loc cf) ∘ (loc cg))(φ)
         = fuse[ ((loc ch) ∘ (loc cf) ∘ (loc cg))(φ) ]
         = fuse[ ((loc ch ∘ cf) ∘ (loc cg))(φ) ]
         = fuse[ (loc ch ∘ cg ∘ cf)(φ) ]
        -}
        via f.hom (prr cg,ch) (fuseLocpath (prr cL,gR) (mapLocpath cf (mapLocpath (prl cg,ch) lp))) $
          refl •
        via fuseLocpath (prr cL,gR') (mapLocpath (prr cg,ch) (mapLocpath cf (mapLocpath (prl cg,ch) lp))) $
          fuse-map-lp (prr cL,gR) (prr cL,gR') (prr cg,ch) (mapLocpath cf (mapLocpath (prl cg,ch) lp)) •
        via fuseLocpath (prr cL,gR') (mapLocpath (prr cg,ch c∘ cf) (mapLocpath (prl cg,ch) lp)) $
          map=
            (fuseLocpath (prr cL,gR'))
            (sym (mapLocpath-c∘ (prr cg,ch) cf (mapLocpath (prl cg,ch) lp)))
          •
        via fuseLocpath (prr cL,gR') (mapLocpath (prr cg,ch c∘ cf c∘ prl cg,ch) lp) $
          map=
            (λ lp' → fuseLocpath (prr cL,gR') lp')
            (sym (mapLocpath-c∘ (prr cg,ch c∘ cf) (prl cg,ch) lp))
          •
        refl
    ))
    
≅.src-id (localizationAdjunction {ℓo}{ℓh}) = nt-ext (λ= cL,gR => λ= cf => functorext (pair-ext
    refl
    (λi= x => λi= y0 => λ= lp0 =>
      --f>< lp := fuse ((loc f>) lp) = ... = f(lp)
      elimd-lp
        (λ y lp →
          fuseLocpath (prr cL,gR) (mapLocpath (nt.obj(≅.fwd (localizationAdjunction{ℓo}{ℓh})) cL,gR cf) lp) == f.hom cf lp)
        (localizationAdjunction:lemma {ℓo}{ℓh} cL,gR cf x)
        (λ y rz rz' p → uip)
        lp0
    )
  ))

≅.tgt-id localizationAdjunction = nt-ext (λ= cL,gR => λ= cf => functorext (pair-ext
    refl
    (λi= x => λi= y => λ= φ => g.m∘runit (prr cL,gR))
  ))
