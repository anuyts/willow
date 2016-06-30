module willow.cat.Groupoids.CoreFunctor where

open import willow.cat.Groupoids public

ccore : {ℓo ℓh : Level} → cCat ℓo ℓh ++> cGrpd ℓo ℓh

f.obj ccore cA = gCore cA

f.obj (f.hom ccore cf) = f.obj cf
f.hom (f.hom ccore cf) {x}{y} η = mapIso cf η
f.hom-id' (f.hom ccore cf) x = ≅ext (f.hom-id' cf x)
f.hom-m∘' (f.hom ccore cf) ψ φ = ≅ext (f.hom-m∘' cf (≅.fwd ψ) (≅.fwd φ))

f.hom-id' ccore cA = functorext (pair-ext refl (λi= x => λi= y => λ= η => ≅ext refl))

f.hom-m∘' ccore {cA}{cB}{cC} cg cf = functorext (pair-ext refl (λi= x => λi= y => λ= η => ≅ext refl))

{-
coreAdjunction : ∀{ℓo ℓh} → cforgetGrpd{ℓo}{ℓh} ⊣ ccore{ℓo}{ℓh}
coreAdjunction = record
  { fwd = record
    -- cf : L → R ; now create a functor cf> : L → core R.
    { obj = λ gL,cR cf → record
          { obj = f.obj cf
          ; hom = λ φ → mapIso cf (g.asIso (prl gL,cR) φ)
          ; hom-id = λ x → ≅ext (f.hom-id' cf x)
          ; hom-m∘ = λ ψ φ → ≅ext (f.hom-m∘' cf ψ φ)
          }
    -- cg : L' → L , ch : R → R' ; now show that (core ch) ∘ cf> ∘ cg = (ch ∘ cf ∘ cg)>
    ; hom = λ cg,ch → λ= cf => functorext (pair-ext refl {!!})
    }
  ; bck = record
    -- cf : L → core R ; now create a functor cf< : L → R
    { obj = λ gL,cR cf → record
          { obj = f.obj cf
          ; hom = λ φ → ≅.fwd (f.hom cf φ)
          ; hom-id = λ x → map= ≅.fwd (f.hom-id' cf x)
          ; hom-m∘ = λ ψ φ → map= ≅.fwd (f.hom-m∘' cf ψ φ)
          }
    -- cg : L' → L , ch : R → R' ; now show that ch ∘ cf< ∘ cg = ((core ch) ∘ cf ∘ cg)<
    ; hom = {!λ cg,ch → λ= cf => ?!}
    }
  ; src-id = nt-ext (λ= gL,cR => λ= cf => functorext (pair-ext refl (
           (Candid-hom (g.cat (prl gL,cR)) (prr gL,cR) (f.obj cf)
           $ (λ φ → ≅.fwd (mapIso cf (g.asIso (prl gL,cR) φ))) == f.hom cf)
           ∋ λi= x => λi= y => λ= φ => refl
        )
      )
    )
  ; tgt-id = nt-ext (λ= gL,cR => λ= cf => functorext (pair-ext refl (
           λi= x => λi= y => λ= φ => ≅ext
           ((c.Hom (prr gL,cR) (f.obj cf x) (f.obj cf y) $ ≅.fwd (f.hom cf φ) == ≅.fwd (f.hom cf φ)) ∋ refl)
        )
      )
    )
    --nt-ext (λ= gL,cR => λ= cf => functorext (pair-ext refl (λi= x => λi= y => λ= φ => ≅ext refl)))
  }
-}
  
{-
cforgetGrpd⊣ccore = record
  { iso = λ {gL cR} → record
    { fwd = λ cf → record
      { obj = λ x → f.obj cf x
      ; hom = λ φ → ≅.fwd (f.hom cf φ)
      ; hom-id = λ x → map= ≅.fwd (f.hom-id' cf x)
      ; hom-m∘ = λ ψ φ → map= ≅.fwd (f.hom-m∘' cf ψ φ)
      }
    ; bck = λ cg → record
      { obj = λ x → f.obj cg x
      ; hom = λ φ → mapIso cg (g.asIso gL φ)
      ; hom-id = λ x → ≅ext (f.hom-id' cg x)
      ; hom-m∘ = λ ψ φ → ≅ext (f.hom-m∘' cg ψ φ)
      }
    ; src-id = λ= cf => functorext (pair-ext refl
        (λi= x => λi= y => λ= φ => ≅ext refl)
      )
    ; tgt-id = λ= cg => functorext (pair-ext refl
        (λi= x => λi= y => λ= φ => refl)
      )
    }
  ; fwd-m∘ = λ {l' l r} ξ φ → functorext (pair-ext refl refl)
  ; bck-m∘ = λ {l r r'} φ ξ → functorext (pair-ext refl
      (λi= x => λi= y => λ= φ => ≅ext refl)
    )
  }
-}
