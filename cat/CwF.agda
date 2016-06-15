module willow.cat.CwF where

open import willow.cat.OfElements public
open import willow.cat.Opposite public
open import willow.cat.Limits public

{-
  -Define tvar as an element of the limit of (Γ, T) ↦ Tm(Γ.T, T[wkn])
  -You get a natural transformation on Ctx^op × ∫ Ty ++> Set, from
    Δ Γ T ↦ Sub Δ Γ.T    to
    Δ Γ T ↦ Sum (σ : Sub Δ Γ) Tm Δ T[σ]
   Define both functors and the NT and require it to be an isomorphism.
-}

record CwF (ℓctx ℓsub ℓty ℓtm : Level) : Set (lsuc (ℓctx ⊔ ℓsub ⊔ ℓty ⊔ ℓtm)) where
  field
    cCtx : Cat ℓctx ℓsub
    
    ∙ : c.Obj cCtx
    ∙isterminal : isTerminal cCtx ∙
    
    c-ty : cOp cCtx ++> cSet ℓty
    c-tm : c∫ {cA = cOp cCtx} c-ty ++> cSet ℓtm
    
    c-compr : cOp∫ c-ty ++> cCtx
    nt-wkn : c-compr nt→ c-co-pr

  -- this is the functor (Γ, T) ↦ (Γ.T, T[wkn])
  f-aux-compr : c∫ c-ty ++> c∫ c-ty
  f.obj f-aux-compr Γ,T = f.obj c-compr Γ,T , f.hom c-ty (nt.obj nt-wkn Γ,T) (prr Γ,T)
  prl (f.hom f-aux-compr σ,p) = f.hom c-compr σ,p
  --note : σ : Δ → Γ (contravariance)
  --show that T[wkn][σ.p] == S[wkn], given p : T[σ] == S
  prr (f.hom f-aux-compr {Γ,T}{Δ,S} σ,p) =
    let Γ = prl Γ,T
        Δ = prl Δ,S
        σ = prl σ,p
        T = prr Γ,T
        S = prr Δ,S
        p = prr σ,p
    in
      via f.hom c-ty (f.hom c-compr σ,p) (f.hom c-ty (nt.obj nt-wkn Γ,T) T) $ refl •
      via f.hom c-ty (cCtx $ nt.obj nt-wkn Γ,T m∘ f.hom c-compr σ,p) T
        $ map= (λ h → h T) (sym (f.hom-m∘ c-ty (f.hom c-compr σ,p) (nt.obj nt-wkn Γ,T))) •
      via f.hom c-ty (cCtx $ f.hom (c-pr {cf = c-ty}) σ,p m∘ nt.obj nt-wkn Δ,S) T
        $ map= (λ ξ → f.hom c-ty ξ T) (sym (nt.hom nt-wkn σ,p)) •
      via f.hom c-ty (nt.obj nt-wkn Δ,S) (f.hom c-ty (f.hom (c-pr {cf = c-ty}) σ,p) T)
        $ map= (λ h → h T) (f.hom-m∘ c-ty (nt.obj nt-wkn Δ,S) (f.hom (c-pr {cf = c-ty}) σ,p)) •
      via f.hom c-ty (nt.obj nt-wkn Δ,S) S
        $ map= (f.hom c-ty (nt.obj nt-wkn Δ,S)) p •
      refl
  f.hom-id f-aux-compr x = pair-ext (f.hom-id c-compr x) uip
  f.hom-m∘ f-aux-compr ψ φ = pair-ext (f.hom-m∘ c-compr φ ψ) uip

  --field
  --  lim-var : Limset (c-tm c∘ f-aux-compr)

  Ctx : Set ℓctx
  Ctx = c.Obj cCtx

  Sub : (Δ Γ : c.Obj cCtx) → Set ℓsub
  Sub Δ Γ = c.Hom cCtx Δ Γ

  _σ∘_ : {Θ Δ Γ : Ctx} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  _σ∘_ = c.comp cCtx

  σ-id : (Γ : Ctx) → Sub Γ Γ
  σ-id = c.id cCtx

  Ty : (Γ : c.Obj cCtx) → Set ℓty
  Ty Γ = f.obj c-ty Γ

  Tsub : {Δ Γ : c.Obj cCtx} (T : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
  Tsub {Δ} {Γ} T σ = f.hom c-ty σ T
  _T[_] = Tsub

  _„_ : (Γ : Ctx) → (T : Ty Γ) → Ctx
  Γ „ T = f.obj c-compr (Γ , T)

  σwkn : {Γ : Ctx} → {T : Ty Γ} → Sub (Γ „ T) Γ
  σwkn {Γ}{T} = nt.obj nt-wkn (Γ , T)

  Tm : (Γ : Ctx) (T : Ty Γ) → Set ℓsub
  Tm Γ T = Sum (λ (t : Sub Γ (Γ „ T)) → σwkn σ∘ t == σ-id Γ)

  tvar : {Γ : Ctx} → {T : Ty Γ} → Tm (Γ „ T) (T T[ σwkn ])
  prl (tvar {Γ}{T}) = {!!}
  prr (tvar {Γ}{T}) = {!!}
