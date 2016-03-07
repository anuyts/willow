
--{-# OPTIONS --no-positivity-check #-}

module aken.cat.Groupoids.CoreAdjunction where

open import aken.cat.Groupoids.CoreFunctor public

private
  coreAdjunction:fwd : ∀{ℓo ℓh} → c.Hom (cExp (cOp (cGrpd ℓo ℓh) c× cCat ℓo ℓh) (cSet _))
    (cHom (cCat ℓo ℓh) c∘ cmap× (c-op cforgetGrpd) (c-id (cCat ℓo ℓh)))
    (cHom (cGrpd ℓo ℓh) c∘ cmap× (c-id (cOp (cGrpd ℓo ℓh))) ccore)
  coreAdjunction:fwd = record
    -- cf : L → R ; now create a functor cf> : L → core R.
    { obj = λ gL,cR cf → record
          { obj = f.obj cf
          ; hom = λ φ → mapIso cf (g.asIso (prl gL,cR) φ)
          ; hom-id = λ x → ≅ext (f.hom-id cf x)
          ; hom-m∘ = λ ψ φ → ≅ext (f.hom-m∘ cf ψ φ)
          }
    -- cg : L' → L , ch : R → R' ; now show that (core ch) ∘ cf> ∘ cg = (ch ∘ cf ∘ cg)>
    ; hom = λ cg,ch → λ= cf => functorext (pair-ext refl {!!})
    }

  coreAdjunction:bck : ∀{ℓo ℓh} → c.Hom (cExp (cOp (cGrpd ℓo ℓh) c× cCat ℓo ℓh) (cSet _))
    (cHom (cGrpd ℓo ℓh) c∘ cmap× (c-id (cOp (cGrpd ℓo ℓh))) ccore)
    (cHom (cCat ℓo ℓh) c∘ cmap× (c-op cforgetGrpd) (c-id (cCat ℓo ℓh)))
  coreAdjunction:bck = record
    -- cf : L → core R ; now create a functor cf< : L → R
    { obj = λ gL,cR cf → record
          { obj = f.obj cf
          ; hom = λ φ → ≅.fwd (f.hom cf φ)
          ; hom-id = λ x → map= ≅.fwd (f.hom-id cf x)
          ; hom-m∘ = λ ψ φ → map= ≅.fwd (f.hom-m∘ cf ψ φ)
          }
    -- cg : L' → L , ch : R → R' ; now show that ch ∘ cf< ∘ cg = ((core ch) ∘ cf ∘ cg)<
    ; hom = {!λ cg,ch → λ= cf => ?!}
    }

coreAdjunction : ∀{ℓo ℓh} → cforgetGrpd{ℓo}{ℓh} ⊣ ccore{ℓo}{ℓh}
coreAdjunction = record
  { fwd = coreAdjunction:fwd
  ; bck = coreAdjunction:bck
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

{-
postulate hole : ∀{ℓ} {A : Set ℓ} → A

coreAdjunction : ∀{ℓo ℓh} → cforgetGrpd{ℓo}{ℓh} ⊣ ccore{ℓo}{ℓh}
coreAdjunction = record
  { fwd = record
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
  ; bck = record
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
