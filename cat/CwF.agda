module willow.cat.CwF where

open import willow.cat.OfElements
open import willow.cat.Opposite

{-
  -Implement cones and limits.
  -Require ∙ to be terminal.
  -Define Tm not as sections, but as a contravariant functor from ∫ Ctx Ty → Set
  -Define tvar as an element of the limit of (Γ, T) ↦ Tm(Γ.T, T[wkn])
  -You get a natural transformation on Ctx^op × ∫ Ty ++> Set, from
    Δ Γ T ↦ Sub Δ Γ.T    to
    Δ Γ T ↦ Sum (σ : Sub Δ Γ) Tm Δ T[σ]
   Define both functors and the NT and require it to be an isomorphism.
-}

record CwF (ℓctx ℓsub ℓty : Level) : Set (lsuc (ℓctx ⊔ ℓsub ⊔ ℓty)) where
  field
    cCtx : Cat ℓctx ℓsub
    c-ty : cOp cCtx ++> cSet ℓty
    c-compr : cOp∫ c-ty ++> cCtx
    nt-pr : c-compr nt→ c-co-pr
    ∙ : c.Obj cCtx
    ∙isterminal : {!!}

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
  σwkn {Γ}{T} = nt.obj nt-pr (Γ , T)

  Tm : (Γ : Ctx) (T : Ty Γ) → Set ℓsub
  Tm Γ T = Sum (λ (t : Sub Γ (Γ „ T)) → σwkn σ∘ t == σ-id Γ)

  tvar : {Γ : Ctx} → {T : Ty Γ} → Tm (Γ „ T) (T T[ σwkn ])
  prl (tvar {Γ}{T}) = {!!}
  prr (tvar {Γ}{T}) = {!!}
