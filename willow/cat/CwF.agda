open import willow.cat.OfElements public
open import willow.cat.Opposite public
open import willow.cat.Limits public
open import willow.cat.Isomorphism public
open import willow.cat.OfElements.DeptPairFunctor public
open import willow.cat.Sets.Limits public
open import willow.cat.HomFunctor
open import willow.basic.TransportLemmas
open import willow.basic.UIP.HeteroIdentity

module willow.cat.CwF where

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
    ∙isterminal : IsTerminal cCtx ∙
    
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
  T[id] {Γ}{T} = map= (λ h → h T) (f.hom-id' c-ty Γ)

  T[][] : {Θ Δ Γ : Ctx} {T : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ} → T T[ σ σ∘ τ ] == (T T[ σ ]) T[ τ ]
  T[][] {Θ}{Δ}{Γ}{T}{σ}{τ} = map= (λ h → h T) (f.hom-m∘' c-ty τ σ)

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

  t[id]' : {Γ : Ctx} {T : Ty Γ} {t : Tm Γ T} → t t[ σ-id Γ ] === t
  --abstract
  t[id]' {Γ}{T}{t} =
      via f.hom c-tm {Γ , T}{Γ , (T T[ σ-id Γ ])} (c.id cCtx Γ , refl) t $ hrefl h•
      via f.hom c-tm {Γ , T}{Γ , T} (c.id (cOp∫ c-ty) (Γ , T)) t $
        (hdmap= (λ T' → λ p → f.hom c-tm {Γ , T}{Γ , T'} (c.id cCtx Γ , p) t) T[id])
        =aph= huip hrefl h•
      to-heter (happly (f.hom-id c-tm (Γ , T)) t)
  t[id] : {Γ : Ctx} {T : Ty Γ} {t : Tm Γ T} → t t[ σ-id Γ ] === t
  t[id] {Γ}{T}{t} = htrust t[id]'

  t[][]' : {Θ Δ Γ : Ctx} {T : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ} {t : Tm Γ T} → t t[ σ σ∘ τ ] === t t[ σ ] t[ τ ]
  --abstract
  t[][]' {Θ}{Δ}{Γ}{T}{σ}{τ}{t} =
      via f.hom c-tm {Γ , T}{Θ , T T[ σ σ∘ τ ]} (cCtx $ σ m∘ τ , refl) t $ hrefl h•
      via f.hom c-tm {Γ , T}{Θ , T T[ σ ] T[ τ ]} (cOp∫ c-ty $ (σ , refl) m∘ (τ , refl)) t $
        (hdmap= (λ T' → λ p → f.hom c-tm {Γ , T}{Θ , T'} (cCtx $ σ m∘ τ , p) t) T[][]) =aph= huip hrefl h•
      to-heter (happly (f.hom-m∘ c-tm (τ , refl) (σ , refl)) t)
  t[][] : {Θ Δ Γ : Ctx} {T : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ} {t : Tm Γ T} → t t[ σ σ∘ τ ] === t t[ σ ] t[ τ ]
  t[][] {Θ}{Δ}{Γ}{T}{σ}{τ}{t} = htrust t[][]'

  -- this is the functor (Γ, T) ↦ (Γ.T, T[wkn])
  c-aux-compr : cOp∫ c-ty ++> cOp∫ c-ty
  c-aux-compr = cOpDeptPair {cA = cCtx} {cCtx} {c-ty} {c-ty} c-compr (c-ty c∘nt nt-op nt-wkn)

  field
    --lim-var is an element of the limit of (Γ, T) ↦ Tm(Γ.T, T[wkn])
    lim-var : Lim (c-tm c∘ c-op c-aux-compr)
        
  tvar : {Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} → f.obj c-tm ((Γ „ T) , (f.hom c-ty σwkn T))
  tvar {Γ}{T} = Lim.obj lim-var (Γ , T)

  field
    pair : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → Sub Δ (Γ „ T)

  _“_ = pair

  field
    wkn-pair' : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → σwkn σ∘ (σ “ t) == σ
    var-pair' : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → tvar{Γ}{T} t[ σ “ t ] === t
    pair-unpair' : {Δ Γ : Ctx} → {T : Ty Γ} → (τ : Sub Δ (Γ „ T)) →
      (σwkn σ∘ τ) “ tra! (trust (map= (Tm Δ) (sym T[][]))) (tvar{Γ}{T} t[ τ ]) == τ

  wkn-pair wkn-pair* : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → σwkn σ∘ (σ “ t) == σ
  abstract wkn-pair* = wkn-pair'
  wkn-pair σ t = trust (wkn-pair* σ t)
  
  var-pair var-pair* : {Δ Γ : Ctx} → {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T T[ σ ])) → tvar{Γ}{T} t[ σ “ t ] === t
  abstract var-pair* = var-pair'
  var-pair σ t = htrust (var-pair* σ t)
  pair-unpair pair-unpair* : {Δ Γ : Ctx} → {T : Ty Γ} → (τ : Sub Δ (Γ „ T)) →
    (σwkn σ∘ τ) “ tra! (trust (map= (Tm Δ) (sym T[][]))) (tvar{Γ}{T} t[ τ ]) == τ
  abstract pair-unpair* = pair-unpair'
  pair-unpair τ = trust (pair-unpair* τ)

  σcompr : {Δ Γ : Ctx} → (σ : Sub Δ Γ) → (T : Ty Γ) → Sub (Δ „ (T T[ σ ])) (Γ „ T)
  σcompr σ T = f.hom c-compr (σ , refl)

  tvar[]' : {Δ Γ : Ctx} {σ : Sub Δ Γ} {T : Ty Γ} → (tvar {Γ}{T}) t[ σcompr σ T ] === tvar {Δ}{T T[ σ ]}
  abstract
    tvar[]' {Δ}{Γ}{σ}{T} =
      via f.hom c-tm {_}{(Δ „ T T[ σ ]) , T T[ σwkn ] T[ σcompr σ T ]}
          (f.hom c-compr (σ , refl) , refl) (tvar{Γ}{T}) $ hrefl h•
      via f.hom c-tm {_}{(Δ „ T T[ σ ]) , T T[ σ ] T[ σwkn ] }
          (f.hom (c-op (cOpDeptPair c-compr (c-ty c∘nt nt-op nt-wkn))) (σ , refl)) (tvar{Γ}{T}) $
        (hdmap= (λ T' → λ p → f.hom c-tm {_}{_ , T'} (f.hom c-compr (σ , refl) , p) (tvar{Γ}{T})) (
          sym T[][] • map= (λ σ' → T T[ σ' ]) (sym (nt.hom nt-wkn (σ , refl))) • T[][]
        )) =aph= huip hrefl h•
      via tvar {Δ}{T T[ σ ]} $ to-heter (Lim.hom lim-var (σ , refl)) h•
      hrefl
  tvar[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} {T : Ty Γ} → (tvar {Γ}{T}) t[ σcompr σ T ] === tvar {Δ}{T T[ σ ]}
  tvar[] = htrust tvar[]'

  σeval : {Γ : Ctx} → {A : Ty Γ} → (a : Tm Γ A) → Sub Γ (Γ „ A)
  σeval {Γ}{A} a = σ-id Γ “ tra! (trust (map= (Tm Γ) (sym T[id]))) a

  abstract
    tvar[σeval]' : {Γ : Ctx} → {A : Ty Γ} → {a : Tm Γ A} → tvar t[ σeval a ] === a
    tvar[σeval]' {Γ}{A}{a} = var-pair (σ-id Γ) (tra! (trust (map= (Tm Γ) (sym T[id]))) a) h•
      hhapply (htra! (trust (map= (Tm Γ) (sym T[id])))) a
  tvar[σeval] : {Γ : Ctx} → {A : Ty Γ} → {a : Tm Γ A} → tvar t[ σeval a ] === a
  tvar[σeval] = htrust tvar[σeval]'

  abstract
   σeval[]' : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {a : Tm Γ A} → (σeval a σ∘ σ) == (σcompr σ A σ∘ σeval (a t[ σ ]))
   σeval[]' {Δ}{Γ}{σ}{A}{a} =
    via σeval a σ∘ σ $ refl •
    via (σwkn σ∘ (σeval a σ∘ σ)) “ tra! (trust (map= (Tm Δ) (sym T[][]))) (tvar t[ σeval a σ∘ σ ]) $
      sym (pair-unpair _) •
    via (σwkn σ∘ (σcompr σ A σ∘ σeval (a t[ σ ]))) “
        tra! (trust (map= (Tm Δ) (sym T[][]))) (tvar t[ σcompr σ A σ∘ σeval (a t[ σ ]) ]) $
      to-homog ((hdmap= _“_
      (
        via σwkn σ∘ (σeval a σ∘ σ) $ refl •
        via (σwkn σ∘ σeval a) σ∘ σ $ sym (c.m∘assoc cCtx) •
        via σ-id Γ σ∘ σ $ map= (λ τ → τ σ∘ σ) (wkn-pair _ _) •
        via σ $ c.m∘lunit cCtx •
        sym (
          via σwkn σ∘ (σcompr σ A σ∘ σeval (a t[ σ ])) $ refl •
          via (σwkn σ∘ σcompr σ A) σ∘ σeval (a t[ σ ]) $ sym (c.m∘assoc cCtx) •
          via (σ σ∘ σwkn) σ∘ σeval (a t[ σ ]) $ map= (λ τ → τ σ∘ σeval (a t[ σ ])) (sym (nt.hom nt-wkn (σ , refl))) •
          via σ σ∘ (σwkn σ∘ σeval (a t[ σ ])) $ c.m∘assoc cCtx •
          via σ σ∘ σ-id Δ $ map= (λ τ → σ σ∘ τ) (wkn-pair _ _) •
          c.m∘runit cCtx
        )
      )) =aph= (
        via tra! (trust (map= (Tm Δ) (sym T[][]))) (tvar t[ σeval a σ∘ σ ]) $ hrefl h•
        via (tvar t[ σeval a σ∘ σ ]) $ hhapply (htra! (trust (map= (Tm Δ) (sym T[][])))) _ h•
        via tsub {T = A T[ σwkn ] T[ σeval a ]} (tvar t[ σeval a ]) σ $ t[][] h•
        via tsub {T = A} a σ $
          (hdmap=
            (λ A' → λ a' → tsub {T = A'} a' σ)
            (sym T[][] • map= (λ σ' → A T[ σ' ]) (wkn-pair _ _) • T[id])
          ) =aph= tvar[σeval] h•
        hsym (
          via tra! (trust (map= (Tm Δ) (sym T[][]))) (tvar t[ σcompr σ A σ∘ σeval (a t[ σ ]) ]) $ hrefl h•
          via tsub {T = A T[ σwkn ]} tvar ( σcompr σ A σ∘ σeval (a t[ σ ]) ) $
            hhapply (htra! (trust (map= (Tm Δ) (sym T[][])))) (tvar t[ σcompr σ A σ∘ σeval (a t[ σ ]) ]) h•
          via tsub {T = A T[ σwkn ] T[ σcompr σ A ]} (tsub {T = A T[ σwkn ]} tvar ( σcompr σ A )) (σeval (a t[ σ ])) $
            t[][] h•
          via tsub {T = A T[ σ ] T[ σwkn ]} tvar (σeval (a t[ σ ])) $
            (hdmap= (λ A' → λ t → tsub {T = A'} t (σeval (a t[ σ ]))) (
              (sym T[][] • map= (λ τ → A T[ τ ]) (sym (nt.hom nt-wkn (σ , refl))) • T[][])
            )) =aph= tvar[] h•
          via a t[ σ ] $ tvar[σeval] h• hrefl
        )
      )) •
    via σcompr σ A σ∘ σeval (a t[ σ ]) $ pair-unpair _ •
    refl
  σeval[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {a : Tm Γ A} → (σeval a σ∘ σ) == (σcompr σ A σ∘ σeval (a t[ σ ]))
  σeval[] = trust σeval[]'

  infix 5 _„_ _“_
  infix 10 _T[_] _t[_]






















  {-
  unpair : {Δ Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} →
    (Lift {ℓ↑ = ℓtm ⊔ ℓsub} (c.Hom cCtx Δ (Γ „ T))) → (Sum λ(σ : c.Hom cCtx Δ Γ) → f.obj c-tm (Δ , f.hom c-ty σ T))
  unpair {Δ}{Γ}{T} = (λ {(lift τ) →
          (cCtx $ σwkn m∘ τ) ,
          (f.hom c-tm (τ , sym (map= (λ f → f T) (f.hom-m∘' c-ty τ σwkn))) tvar)
        })

  field
    canpair : {Δ Γ : c.Obj cCtx} → {T : f.obj c-ty Γ} →
      IsIso (cSet (ℓtm ⊔ ℓsub))
        {Lift {ℓ↑ = ℓtm ⊔ ℓsub} (c.Hom cCtx Δ (Γ „ T))}
        {Sum λ(σ : c.Hom cCtx Δ Γ) → f.obj c-tm (Δ , f.hom c-ty σ T)}
        unpair

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
  -}





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
  _++>_.hom-id' cSubAndTerm = λ {(Δ , (Γ , T)) → λ= σ,t => pair-hext
        (map= (λ h → h (prl σ,t)) (f.hom-id' (cHom cCtx) (Δ , Γ)))
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
  _++>_.hom-m∘' cSubAndTerm ψ φ = {!!}
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
          (f.hom c-tm (τ , sym (map= (λ f → f T) (f.hom-m∘' c-ty τ σwkn))) tvar)
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
  T[][] {T = T}{σ}{τ} = map= (λ h → h T) (f.hom-m∘' c-ty τ σ)

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
  f.hom-id' c-compr Γ,T =
    let Γ = prl Γ,T
        T = prr Γ,T
    in  {!!}
  f.hom-m∘' c-compr ψ φ = {!!}
-}
