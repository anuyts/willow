
--{-# OPTIONS --no-positivity-check #-}

module willow.cat.Groupoids.CoreAdjunction where

open import willow.cat.Groupoids.CoreFunctor public

postulate hole : ∀{ℓ} {A : Set ℓ} → A

coreAdjunction : ∀{ℓo ℓh} → cforgetGrpd{ℓo}{ℓh} ⊣ ccore{ℓo}{ℓh}
≅.fwd coreAdjunction = record
    -- cf : L → R ; now create a functor cf> : L → core R.
    { obj = λ gL,cR cf → record
          { obj = f.obj cf
          ; hom = λ φ → mapIso cf (g.asIso (prl gL,cR) φ)
          ; hom-id = λ x → ≅ext (f.hom-id cf x)
          ; hom-m∘ = λ ψ φ → ≅ext (f.hom-m∘ cf ψ φ)
          }
    -- cg : L' → L , ch : R → R' ; now show that (core ch) ∘ cf> ∘ cg = (ch ∘ cf ∘ cg)>
    ; hom = λ cg,ch → λ= cf => functorext (pair-ext refl hole)
    }
≅.bck coreAdjunction = record
    -- cf : L → core R ; now create a functor cf< : L → R
    { obj = λ gL,cR cf → record
          { obj = f.obj cf
          ; hom = λ φ → ≅.fwd (f.hom cf φ)
          ; hom-id = λ x → map= ≅.fwd (f.hom-id cf x)
          ; hom-m∘ = λ ψ φ → map= ≅.fwd (f.hom-m∘ cf ψ φ)
          }
    -- cg : L' → L , ch : R → R' ; now show that ch ∘ cf< ∘ cg = ((core ch) ∘ cf ∘ cg)<
    ; hom = hole -- {!λ cg,ch → λ= cf => ?!}
    }
≅.src-id coreAdjunction = nt-ext (λ= gL,cR => λ= cf => functorext (pair-ext refl (
           (Candid-hom (g.cat (prl gL,cR)) (prr gL,cR) (f.obj cf)
           $ (λ φ → ≅.fwd (mapIso cf (g.asIso (prl gL,cR) φ))) == f.hom cf)
           ∋ λi= x => λi= y => λ= φ => refl
        )
      )
    )
≅.tgt-id coreAdjunction = nt-ext (λ= gL,cR => λ= cf => functorext (pair-ext refl (
           λi= x => λi= y => λ= φ => ≅ext
           ((c.Hom (prr gL,cR) (f.obj cf x) (f.obj cf y) $ ≅.fwd (f.hom cf φ) == ≅.fwd (f.hom cf φ)) ∋ refl)
        )
      )
    )
    --nt-ext (λ= gL,cR => λ= cf => functorext (pair-ext refl (λi= x => λi= y => λ= φ => ≅ext refl)))
