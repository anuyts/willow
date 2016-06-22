module willow.cat.CwF where

open import willow.cat.OfElements public
open import willow.cat.Opposite public
open import willow.cat.Limits public
open import willow.cat.Isomorphism public
open import willow.cat.OfElements.DeptPairFunctor public
open import willow.cat.Sets.Limits public
open import willow.cat.HomFunctor
open import willow.basic.TransportLemmas
open import willow.basic.Propositional.HeteroIdentity

{-
  -You get a natural transformation on Ctx^op × ∫ Ty ++> Set, from
    Δ Γ T ↦ Sub Δ Γ.T    to
    Δ Γ T ↦ Sum (σ : Sub Δ Γ) Tm Δ T[σ]
   Define both functors and the NT and require it to be an isomorphism.
-}
record CwF (ℓctx ℓsub ℓty ℓtm : Level) : Set (lsuc (ℓctx ⊔ ℓsub ⊔ ℓty ⊔ ℓtm)) where
  no-eta-equality
  field
    cCtx : Cat ℓctx ℓsub
    
    ∙ : c.Obj cCtx
    ∙isterminal : [IsTerminal] cCtx ∙
    
    c-ty : cOp cCtx ++> cSet ℓty
    c-tm : cOp (cOp∫ {cA = cOp cCtx} c-ty) ++> cSet ℓtm
    
    c-compr : cOp∫ c-ty ++> cCtx
    nt-wkn : c-compr nt→ c-co-pr

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

  T[id] : {Γ : Ctx} {T : Ty Γ} → T T[ σ-id Γ ] == T
  T[id] {Γ}{T} = map= (λ h → h T) (f.hom-id c-ty Γ)

  T[][] : {Θ Δ Γ : Ctx} {T : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ} → T T[ σ σ∘ τ ] == (T T[ σ ]) T[ τ ]
  T[][] {Θ}{Δ}{Γ}{T}{σ}{τ} = map= (λ h → h T) (f.hom-m∘ c-ty τ σ)

  _„_ : (Γ : Ctx) → (T : Ty Γ) → Ctx
  _„_ Γ T = f.obj c-compr (Γ , T)

  σwkn : {Γ : Ctx} → {T : Ty Γ} → Sub (Γ „ T) Γ
  σwkn {Γ}{T} = nt.obj nt-wkn (Γ , T)

  Tm : (Γ : Ctx) (T : Ty Γ) → Set ℓtm
  Tm Γ T = f.obj c-tm (Γ , T)
  --Tm Γ T = Sum (λ (t : Sub Γ (Γ „ T)) → σwkn σ∘ t == σ-id Γ)

  tsub : {Δ Γ : Ctx} {T : Ty Γ} (t : Tm Γ T) (σ : Sub Δ Γ) → Tm Δ (T T[ σ ])
  tsub t σ = f.hom c-tm (σ , refl) t
  _t[_] = tsub

  -- this is the functor (Γ, T) ↦ (Γ.T, T[wkn])
  c-aux-compr : cOp∫ c-ty ++> cOp∫ c-ty
  c-aux-compr = cOpDeptPair {cA = cCtx} {cCtx} {c-ty} {c-ty} c-compr (c-ty c∘nt nt-op nt-wkn)

  field
    --lim-var is an element of the limit of (Γ, T) ↦ Tm(Γ.T, T[wkn])
    lim-var : Lim (c-tm c∘ c-op c-aux-compr)
        
  tvar : {Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} → f.obj c-tm ((Γ „ T) , (f.hom c-ty σwkn T))
  tvar {Γ}{T} = Lim.obj lim-var (Γ , T)

  field
    canpair : {Δ Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} →
      IsIso (cSet (ℓtm ⊔ ℓsub))
        {Lift {ℓ↑ = ℓtm ⊔ ℓsub} (c.Hom cCtx Δ (Γ „ T))}
        {Sum λ(σ : c.Hom cCtx Δ Γ) → f.obj c-tm (Δ , f.hom c-ty σ T)}
        (λ {(lift τ) →
          (cCtx $ σwkn m∘ τ) ,
          (f.hom c-tm (τ , sym (map= (λ f → f T) (f.hom-m∘ c-ty τ σwkn))) tvar)
        })

  i-unpair : {Δ Γ : Ctx} → {T : Ty Γ} →
      Iso (cSet (ℓtm ⊔ ℓsub))
        (Lift {ℓ↑ = ℓtm ⊔ ℓsub} (Sub Δ (Γ „ T)))
        (Sum λ(σ : Sub Δ Γ) → Tm Δ (T T[ σ ]))
  i-unpair = i-refurbish (cSet (ℓtm ⊔ ℓsub)) canpair

  i-pair : {Δ Γ : Ctx} → {T : Ty Γ} →
      Iso (cSet (ℓtm ⊔ ℓsub))
        (Sum λ(σ : Sub Δ Γ) → Tm Δ (T T[ σ ]))
        (Lift {ℓ↑ = ℓtm ⊔ ℓsub} (Sub Δ (Γ „ T)))
  i-pair = i-inv (cSet (ℓtm ⊔ ℓsub)) i-unpair

  _“_ : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → Sub Δ (Γ „ T)
  σ “ t = lower (≅.fwd i-pair (σ , t))

  -- this is the functor (Δ, (Γ, T)) ↦ Sub Δ Γ.T
  cSubIntoCompr : cOp cCtx c× cOp∫ c-ty ++> cSet ℓsub
  cSubIntoCompr = cHom cCtx c∘ (c-prl (cOp cCtx) (cOp∫ c-ty) c⊠ c-compr c∘ c-prr (cOp cCtx) (cOp∫ c-ty))

--  t[id] : {Γ : Ctx} {T : Ty Γ} {t : Tm Γ T} → t t[ σ-id Γ ] === t
--  t[id] {Γ}{T}{t} rewrite toAgdaEq (sym (T[id] {Γ} {T})) = {!prr (c.id (cOp∫ c-ty) (Γ , T))!}

  {-
  -- this is the functor (Δ, (Γ, T)) ↦ Sum (σ : Sub Δ Γ) Tm Δ T[σ]
  cSubAndTerm : cOp cCtx c× cOp∫ c-ty ++> cSet (ℓsub ⊔ ℓtm)
  _++>_.obj cSubAndTerm = λ Δ,Γ,T →
          let Δ = prl Δ,Γ,T
              Γ = prl (prr Δ,Γ,T)
              T = prr (prr Δ,Γ,T)
          in  Sum λ (σ : Sub Δ Γ) → Tm Δ (T T[ σ ])
  _++>_.hom cSubAndTerm = λ {Δ,Γ,T} {Δ',Γ',T'} δ,γ,p σ,t →
          let Δ = prl Δ,Γ,T
              Γ = prl (prr Δ,Γ,T)
              T = prr (prr Δ,Γ,T)
              Δ' = prl Δ',Γ',T'
              Γ' = prl (prr Δ',Γ',T')
              T' = prr (prr Δ',Γ',T')
              δ = prl δ,γ,p
              γ = prl (prr δ,γ,p)
              p = prr (prr δ,γ,p)
              σ = prl σ,t
              t = prr σ,t
          in  f.hom (cHom cCtx) (δ , γ) σ , (tra Tm Δ' /
                via T T[ σ ] T[ δ ] $ refl •
                via T' T[ γ ] T[ σ ] T[ δ ] $ map= (λ S → S T[ σ ] T[ δ ]) (sym p) •
                via T' T[ γ σ∘ σ ] T[ δ ] $ map= (λ S → S T[ δ ]) (sym T[][]) •
                via T' T[ (γ σ∘ σ) σ∘ δ ] $ (sym T[][]) • 
                via T' T[ f.hom (cHom cCtx) (δ , γ) σ ] $ map= (λ τ → T' T[ τ ]) refl • refl
              of (t t[ δ ]))
  _++>_.hom-id cSubAndTerm = λ {(Δ , (Γ , T)) → λ= σ,t => pair-hext
        (map= (λ h → h (prl σ,t)) (f.hom-id (cHom cCtx) (Δ , Γ)))
        (
          (htra (Tm Δ) / _ of ((prr σ,t) t[ c.id cCtx Δ ])) h• {!!}
        )
        {-(
          map= (tra (λ σ → Tm Δ (T T[ σ ])) / _) (tra-canon {B = Tm Δ} {b = (prr σ,t) t[ c.id cCtx Δ ]}) •
          tra-canon
            {B = (λ σ → Tm Δ (T T[ σ ]))}
            {b = (tra idf / map= (Tm Δ) _ of (prr σ,t t[ Cat.id cCtx Δ ]))} •
          tra-comp {B = idf} {p = map= (Tm Δ) _} {q = map= (λ σ → Tm Δ (T T[ σ ])) _} {b = (prr σ,t) t[ c.id cCtx Δ ]} •
          via {!tra idf / refl of (prr σ,t t[ Cat.id cCtx Δ ])!} $ {!!} •
          {!!}
          --tra-canon {B = (λ σ → Tm Δ (T T[ σ ]))} • {!!}
          --(map= (tra (λ σ → Tm Δ (T T[ σ ])) / _) tra-canon • tra-canon • tra-comp • {!!})
        )-}
      }
  _++>_.hom-m∘ cSubAndTerm ψ φ = {!!}
  -}


--This is leading nowhere!
{-
record CwF' (ℓctx ℓsub ℓty ℓtm : Level) : Set (lsuc (ℓctx ⊔ ℓsub ⊔ ℓty ⊔ ℓtm)) where
  field
    cCtx : Cat ℓctx ℓsub

    ∙ : c.Obj cCtx
    ∙isterminal : IsTerminal cCtx ∙
    
    c-ty : cOp cCtx ++> cSet ℓty
    c-tm : c∫ {cA = cOp cCtx} c-ty ++> cSet ℓtm

    _„_ : (Γ : c.Obj cCtx) → (T : f.obj c-ty Γ) → c.Obj cCtx
    σwkn : {Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} → c.Hom cCtx (Γ „ T) Γ
    tvar : {Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} → f.obj c-tm ((Γ „ T) , (f.hom c-ty σwkn T))

    canpair : {Δ Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} →
      IsIso (cSet (ℓtm ⊔ ℓsub))
        {Lift {ℓ↑ = ℓtm ⊔ ℓsub} (c.Hom cCtx Δ (Γ „ T))}
        {Sum λ(σ : c.Hom cCtx Δ Γ) → f.obj c-tm (Δ , f.hom c-ty σ T)}
        (λ {(lift τ) →
          (cCtx $ σwkn m∘ τ) ,
          (f.hom c-tm (τ , sym (map= (λ f → f T) (f.hom-m∘ c-ty τ σwkn))) tvar)
        })

  --simpler names
  Ctx : Set ℓctx
  Ctx = c.Obj cCtx

  Sub : (Δ Γ : Ctx) → Set ℓsub
  Sub Δ Γ = c.Hom cCtx Δ Γ

  _σ∘_ : {Θ Δ Γ : Ctx} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  _σ∘_ = c.comp cCtx

  σ-id : (Γ : Ctx) → Sub Γ Γ
  σ-id = c.id cCtx

  Ty : (Γ : Ctx) → Set ℓty
  Ty Γ = f.obj c-ty Γ

  Tsub : {Δ Γ : Ctx} (T : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
  Tsub {Δ} {Γ} T σ = f.hom c-ty σ T
  _T[_] = Tsub

  T[][] : {Θ Δ Γ : c.Obj cCtx} {T : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ} → T T[ σ σ∘ τ ] == (T T[ σ ]) T[ τ ]
  T[][] {T = T}{σ}{τ} = map= (λ h → h T) (f.hom-m∘ c-ty τ σ)

  Tm : (Γ : Ctx) (T : Ty Γ) → Set ℓtm
  Tm Γ T = f.obj c-tm (Γ , T)

  --defining objects with simpler types
  _„'_ : (Γ : Ctx) → (T : Ty Γ) → Ctx
  _„'_ = _„_
  σwkn' : {Γ : Ctx} → {T : Ty Γ} → Sub (Γ „ T) Γ
  σwkn' = σwkn
  tvar' : {Γ : Ctx} → {T : Ty Γ} → Tm (Γ „ T) (T T[ σwkn ])
  tvar' = tvar

  i-unpair : {Δ Γ : Ctx} → {T : Ty Γ} →
      Iso (cSet (ℓtm ⊔ ℓsub))
        (Lift {ℓ↑ = ℓtm ⊔ ℓsub} (Sub Δ (Γ „ T)))
        (Sum λ(σ : Sub Δ Γ) → Tm Δ (T T[ σ ]))
  i-unpair = i-refurbish (cSet (ℓtm ⊔ ℓsub)) canpair

  i-pair : {Δ Γ : Ctx} → {T : Ty Γ} →
      Iso (cSet (ℓtm ⊔ ℓsub))
        (Sum λ(σ : Sub Δ Γ) → Tm Δ (T T[ σ ]))
        (Lift {ℓ↑ = ℓtm ⊔ ℓsub} (Sub Δ (Γ „ T)))
  i-pair = i-inv (cSet (ℓtm ⊔ ℓsub)) i-unpair

  _“_ : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → Sub Δ (Γ „ T)
  σ “ t = lower (≅.fwd i-pair (σ , t))

  c-compr : cOp∫ c-ty ++> cCtx
  f.obj c-compr Γ,T = prl Γ,T „ prr Γ,T
  f.hom c-compr {Δ,Tσ} {Γ,T} σ,p =
    let Δ = prl Δ,Tσ
        Tσ = prr Δ,Tσ
        Γ = prl Γ,T
        T = prr Γ,T
        σ = prl σ,p
        p = prr σ,p
        q : (Tσ T[ σwkn ]) == (T T[ σ σ∘ σwkn ])
        q = map= (λ S → S T[ σwkn ]) (sym p) • sym T[][]
    in  (σ σ∘ σwkn) “ (tra Tm (Δ „ Tσ) / q of tvar)
  f.hom-id c-compr Γ,T =
    let Γ = prl Γ,T
        T = prr Γ,T
    in  {!!}
  f.hom-m∘ c-compr ψ φ = {!!}
-}
