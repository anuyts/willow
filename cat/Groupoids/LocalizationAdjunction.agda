module willow.cat.Groupoids.LocalizationAdjunction where

open import willow.cat.Groupoids.LocalizationFunctor public

localizationAdjunction : ∀{ℓo ℓh} → cloc{ℓo}{ℓo ⊔ ℓh} ⊣ cforgetGrpd{ℓo}{ℓo ⊔ ℓh}
≅.fwd localizationAdjunction = record
  -- cf : loc L → R ; now create functor cf> : L → R
  { obj = λ cL,gR → λ cf → record
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
  ; hom = λ cg,ch → λ= cf => functorext (pair-ext refl refl)
  }
≅.bck localizationAdjunction = record
  -- cf : L → R ; now create functor cf< : loc L → R
  { obj = λ cL,gR → λ cf → record
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
  -- f.hom LHS = ch ∘ fuse ∘ (loc cf) ∘ (loc cg).
  -- f.hom RHS = fuse ∘ (loc (ch ∘ cf ∘ cg))
  ; hom = λ {cL,gR}{cL,gR'} cg,ch → λ= cf => functorext (pair-ext refl (λi= x => λi= y0 => λ= lp0 =>
        elimd-lp
          (λ y lp →
            f.hom (prr cg,ch) (fuseLocpath (prr cL,gR) (mapLocpath cf (mapLocpath (prl cg,ch) lp))) ==
            fuseLocpath (prr cL,gR') (mapLocpath ((prr cg,ch) c∘ cf c∘ (prl cg,ch)) lp)
          )
          (λ y rz → {!!})
          (λ y rz rz' p → uip)
          lp0
    ))
  }
≅.src-id localizationAdjunction = {!!}
≅.tgt-id localizationAdjunction = {!!}
