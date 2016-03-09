module willow.cat.Groupoids.LocalizationAdjunction where

open import willow.cat.Groupoids.LocalizationFunctor public

localizationAdjunction : ∀{ℓo ℓh} → cloc{ℓo}{ℓo ⊔ ℓh} ⊣ cforgetGrpd{ℓo}{ℓo ⊔ ℓh}

-- cf : loc L → R ; now create functor cf> : L → R
nt.obj (≅.fwd localizationAdjunction) cL,gR cf = record
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
    
≅.src-id localizationAdjunction = {!!}
≅.tgt-id localizationAdjunction = {!!}
