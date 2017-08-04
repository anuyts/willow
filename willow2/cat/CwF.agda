{-# OPTIONS --type-in-type --rewriting #-}

module willow2.cat.CwF where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open import willow2.basic.HeterogeneousEquality public

--TODO: split up into CwF and IsCwF
--{-# BUILTIN REWRITE _≡_ #-}

cFam : Cat
ℓo cFam = ℓ?
ℓh cFam = ℓ?
Obj cFam = Σ[ Ty ∈ Set ] (Ty → Set)
Hom cFam (Ty1 , Tm1) (Ty2 , Tm2) = Σ[ tysub ∈ (Ty1 → Ty2) ] ((T : Ty1) → Tm1 T → Tm2 (tysub T))
IsCat.id⟨ isCat cFam ⟩ (Ty , Tm) = f-id , (λ T → f-id)
IsCat._∘_ (isCat cFam) (tysub2 , tmsub2) (tysub1 , tmsub1) = (tysub2 f∘ tysub1) , (λ T → tmsub2 _ f∘ tmsub1 T)
IsCat.assoc (isCat cFam) ψ ξ φ = refl
IsCat.lunit (isCat cFam) φ = refl
IsCat.runit (isCat cFam) φ = refl

record IsCwF {Ctx : Set} (Sub : Ctx → Ctx → Set) {Ty : Ctx → Set} (Tm : (Γ : Ctx) → Ty Γ → Set) : Set where
  field
    {{isCat}} : IsCat Sub
    _⟦_⟧ : ∀ {Δ Γ} → Ty Γ → (σ : Sub Δ Γ) → Ty Δ
    .{{tysub-id}} : ∀{Γ} {T : Ty Γ} → T ⟦ id ⟧ ≡ T
    .{{tysub-comp}} : ∀{Θ Δ Γ} {T : Ty Γ} (σ : Sub Δ Γ) (τ : Sub Θ Δ) → T ⟦ σ ∘ τ ⟧ ≡ T ⟦ σ ⟧ ⟦ τ ⟧
    _[_] : ∀ {Δ Γ} {T : Ty Γ} (t : Tm Γ T) → (σ : Sub Δ Γ) → Tm Δ (T ⟦ σ ⟧)
    .{{tmsub-id}} : ∀{Γ} {T : Ty Γ} {t : Tm Γ T} → t [ id ] ≅ t
    .{{tmsub-comp}} : ∀{Θ Δ Γ} {T : Ty Γ} {t : Tm Γ T} (σ : Sub Δ Γ) (τ : Sub Θ Δ) → t [ σ ∘ τ ] ≅ t [ σ ] [ τ ]
    
  cCtx : Cat
  cCtx = cat Sub

  field
    ‚ : Ctx
    ‘ : ∀{Γ} → Sub Γ ‚
    .{{ext-‚}} : ∀{Γ} {σ : Sub Γ ‚} → σ ≡ ‘
    _„_ : (Γ : Ctx) → Ty Γ → Ctx
    _“_ : ∀{Δ Γ} {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T ⟦ σ ⟧)) → Sub Δ (Γ „ T)
    π : ∀{Γ} {T : Ty Γ} → Sub (Γ „ T) Γ
    ξ : ∀{Γ} {T : Ty Γ} → Tm (Γ „ T) (T ⟦ π ⟧)
    .{{π∘“}} : ∀{Δ Γ} {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T ⟦ σ ⟧)) → π ∘ (σ “ t) ≡ σ
    .{{ξ[“]}} : ∀{Δ Γ} {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (T ⟦ σ ⟧)) → ξ [ σ “ t ] ≅ t
    .{{ext-„}} : ∀{Δ Γ} {T : Ty Γ} → {σ τ : Sub Δ (Γ „ T)} → π ∘ σ ≡ π ∘ τ → ξ [ σ ] ≅ ξ [ τ ] → σ ≡ τ

  c-fam : cOp cCtx c→ cFam
  obj c-fam Γ = (Ty Γ) , (Tm Γ)
  hom c-fam σ = (λ T → T ⟦ σ ⟧) , (λ T t → t [ σ ])
  hom-id c-fam = ext-Σ (λ= T , tysub-id) (λ≅ T , λ≅ t , tmsub-id)
  hom-comp c-fam σ τ = ext-Σ (λ= T , tysub-comp _ _) (λ≅ T , λ≅ t , tmsub-comp _ _)

{-
  c-ty : cOp cCtx c→ cSet _
  obj c-ty = Ty
  hom c-ty σ T = T ⟦ σ ⟧
  hom-id c-ty = λ= T , tysub-id
  hom-comp c-ty σ τ = λ= T , tysub-comp _ _

  c-tm : cOp (c∫⁻ cCtx c-ty) c→ cSet _
  obj c-tm (Γ , T) = Tm Γ T
  hom c-tm {Γ , T} {Δ , S} (σ , eσ) t with choose eσ
  hom c-tm {Γ , T} {Δ , .(T ⟦ σ ⟧)} (σ , eσ) t | refl = t [ σ ]
  hom-id c-tm {Γ , T} with T ⟦ id ⟧ | choose (wit (id {{isCat (c∫⁻ cCtx c-ty)}} {Γ , T}))
  hom-id c-tm {Γ , T} | .T | refl = {!!}
  hom-comp c-tm = {!!}
-}

open IsCwF {{...}} public

record CwF : Set where
  constructor cwf
  field
    Ctx : Set
    Sub : Ctx → Ctx → Set
    Ty : Ctx → Set
    Tm : (Γ : Ctx) → Ty Γ → Set
    {{isCwF}} : IsCwF Sub Tm
open CwF public

{-
record IsCwF (cCtx : Cat)(c-ty : cOp cCtx c→ cSet _)(c-tm : cOp (c∫⁻ cCtx c-ty) c→ cSet _) : Set where
  field
    ∙ : Obj cCtx
    ∙isterminal : IsTerminal cCtx ∙
    
    --c-compr : c∫⁻ cCtx c-ty c→ cCtx
    --nt-π : c-compr nt→ c-proj⁻ c-ty

    _„_ : (Γ : Obj cCtx) → (T : obj c-ty Γ) → Obj cCtx

    π : ∀{Γ T} → Hom cCtx (Γ „ T) Γ
    ξ : ∀{Γ T} → obj c-tm ((Γ „ T) , hom c-ty π T)
    _“_ : ∀{Δ Γ T} → (σ : Hom cCtx Δ Γ) → (t : obj c-tm (Δ , hom c-ty σ T)) → Hom cCtx Δ (Γ „ T)

    .π“ : ∀{Δ Γ T} {σ : Hom cCtx Δ Γ} {t : obj c-tm (Δ , hom c-ty σ T)} → π ∘ (σ “ t) ≡ σ
    .ξ“ : ∀{Δ Γ T} {σ : Hom cCtx Δ Γ} {t : obj c-tm (Δ , hom c-ty σ T)} →
      hom c-tm ((σ “ t) , (begin
        hom c-ty (σ “ t) (hom c-ty π T)
          ≡⟨ cong-app (sym (hom-comp c-ty _ _)) T ⟩
        hom c-ty (π ∘ (σ “ t)) T
          ≡⟨ cong (λ τ → hom c-ty τ T) π“ ⟩
        hom c-ty σ T ∎
        )) ξ ≡ t
    .π“ξ : ∀{Γ T} → (π “ ξ) ≡ id⟨ Γ „ T ⟩
open IsCwF {{...}} public

record CwF : Set where
  constructor cwf
  field
    cCtx : Cat
    c-ty : cOp cCtx c→ cSet _
    c-tm : cOp (c∫⁻ cCtx c-ty) c→ cSet _
    {{isCwF}} : IsCwF cCtx c-ty c-tm

  Ctx = Obj cCtx
  Sub = Hom* cCtx

  --infix 4 _σ→_

  Ty : (Γ : Ctx) → Set _
  Ty Γ = obj c-ty Γ
open CwF public

module IsCwF*
  {cCtxA : Cat}
  {c-tyA : cOp cCtxA c→ cSet _}
  {c-tmA : cOp (c∫⁻ cCtxA c-tyA) c→ cSet _}
  {{isCwF : IsCwF cCtxA c-tyA c-tmA}} where
  cwfA = cwf cCtxA c-tyA c-tmA

  postulate
    π* : ∀{Γ : Ctx cwfA} {T : Ty cwfA Γ} → Sub cwfA (Γ „ T) Γ

open IsCwF* public
-}

{-
record CwF : Setω where
  field
    cCtx : Cat
    
    ∙ : Obj cCtx
    .{{∙IsTerminal}} : IsTerminal cCtx ∙

    c-ty : cOp cCtx c→ cSet _
    c-tm : cOp (c∫⁻ cCtx c-ty) c→ cSet _

    _„_ : (Γ : Obj cCtx) → (T : obj c-ty Γ) → Obj cCtx

    π : ∀{Γ T} → Hom cCtx (Γ „ T) Γ
    ξ : ∀{Γ T} → obj c-tm ((Γ „ T) , hom c-ty π T)
    _“_ : ∀{Δ Γ T} → (σ : Hom cCtx Δ Γ) → (t : obj c-tm (Δ , hom c-ty σ T)) → Hom cCtx Δ (Γ „ T)

    .π“ : ∀{Δ Γ T} {σ : Hom cCtx Δ Γ} {t : obj c-tm (Δ , hom c-ty σ T)} → π ∘ (σ “ t) ≡ σ
    .ξ“ : ∀{Δ Γ T} {σ : Hom cCtx Δ Γ} {t : obj c-tm (Δ , hom c-ty σ T)} →
      hom c-tm ((σ “ t) , (begin
        hom c-ty (σ “ t) (hom c-ty π T)
          ≡⟨ cong-app (sym (hom-comp c-ty _ _)) T ⟩
        hom c-ty (π ∘ (σ “ t)) T
          ≡⟨ cong (λ τ → hom c-ty τ T) π“ ⟩
        hom c-ty σ T ∎
        )) ξ ≡ t
    .π“ξ : ∀{Γ T} → (π “ ξ) ≡ id⟨ Γ „ T ⟩

  Ctx = Obj cCtx
  _σ→_ = Hom cCtx

  infix 4 _σ→_

  Ty : (Γ : Ctx) → Set _
  Ty Γ = obj c-ty Γ

  Tm : (Γ : Ctx) (T : Ty Γ) → Set _
  Tm Γ T = obj c-tm (Γ , T)

  _⟦_⟧ : ∀{Δ Γ} (T : Ty Γ) (σ : Δ σ→ Γ) → Ty Δ
  T ⟦ σ ⟧ = hom c-ty σ T
  .tysub-id : ∀{Γ} {T : Ty Γ} → T ⟦ id ⟧ ≡ T
  tysub-id {Γ}{T} = cong-app (hom-id c-ty) T
  .tysub-comp : ∀{Θ Δ Γ} {τ : Θ σ→ Δ} {σ : Δ σ→ Γ} {T : Ty Γ} → T ⟦ σ ∘ τ ⟧ ≡ T ⟦ σ ⟧ ⟦ τ ⟧
  tysub-comp = cong-app (hom-comp c-ty _ _) _

  .tysub-id' : ∀{Γ} {T : Ty Γ} → hom c-ty id T ≡ T
  tysub-id' = tysub-id

  _[_] : ∀{Δ Γ} {T : Ty Γ} (t : Tm Γ T) (σ : Δ σ→ Γ) → Tm Δ (T ⟦ σ ⟧)
  t [ σ ] = hom c-tm (σ , refl) t
  .tmsub-id : ∀{Γ T} {t : Tm Γ T} → t [ id ] ≅ t
  tmsub-id {Γ}{T}{t} = hbegin
    (Tm Γ (T ⟦ id ⟧) ∋ hom c-tm (id , refl) t)
      ≅⟨ hcong₂
           (λ (T' : Ty Γ) (σ* : Hom (c∫⁻ cCtx c-ty) (Γ , T') (Γ , T)) → Tm Γ T' ∋ hom c-tm σ* t)
           (≡-to-≅ tysub-id)
           (hext-Subset refl (≡-to-≅ (cong (λ T' → λ σ → T ⟦ σ ⟧ ≡ T') tysub-id)))
       ⟩
    (Tm Γ T ∋ hom c-tm (IsCat.id (isCat (c∫⁻ cCtx c-ty))) t)
      ≅⟨ ≡-to-≅ (cong-app (hom-id c-tm) t) ⟩
    (Tm Γ T ∋ t) h∎
  .tmsub-comp : ∀{Θ Δ Γ} {τ : Θ σ→ Δ} {σ : Δ σ→ Γ} {T} {t : Tm Γ T} → t [ σ ∘ τ ] ≅ t [ σ ] [ τ ]
  tmsub-comp {Θ}{Δ}{Γ}{τ}{σ}{T}{t} = hbegin
    (Tm Θ (T ⟦ σ ∘ τ ⟧) ∋ hom c-tm (σ ∘ τ , refl) t)
      ≅⟨ hcong₂
           (λ (T' : Ty Θ) (ρ* : Hom (c∫⁻ cCtx c-ty) (Θ , T') (Γ , T)) → Tm Θ T' ∋ hom c-tm ρ* t)
           (≡-to-≅ tysub-comp)
           (hext-Subset refl (≡-to-≅ (cong (λ T' → λ ρ → T ⟦ ρ ⟧ ≡ T') tysub-comp)))
       ⟩
    (Tm Θ (T ⟦ σ ⟧ ⟦ τ ⟧) ∋ hom c-tm (σ ∘ τ , _) t)
      ≅⟨ ≡-to-≅ (cong-app (hom-comp c-tm _ _) t) ⟩
    (Tm Θ (T ⟦ σ ⟧ ⟦ τ ⟧) ∋ t [ σ ] [ τ ]) h∎

  infixl 5 _„_ _“_
  infix 10 _⟦_⟧ _[_]

  _& : ∀{Δ Γ} {T : Ty Γ} (σ : Δ σ→ Γ) → ((Δ „ T ⟦ σ ⟧) σ→ (Γ „ T))
  _& {Δ}{Γ}{T} σ = σ ∘ π “ (ξ !> cong (Tm (Δ „ T ⟦ σ ⟧)) (sym tysub-comp))

  c-compr : c∫⁻ cCtx c-ty c→ cCtx
  obj c-compr (Γ , T) = Γ „ T
  hom c-compr {Δ , T⟦σ⟧} {Γ , T} (σ , eσ) = (σ &) !> cong (λ T' → Hom cCtx (Δ „ T') (Γ „ T)) eσ
  hom-id c-compr {Γ , T} = ≅-to-≡ (hbegin
    ((Γ „ T σ→ Γ „ T) ∋ (id &) !> _)
      ≅⟨ !>≅ ⟩
    ((Γ „ T ⟦ id ⟧ σ→ Γ „ T) ∋ id &)
      ≅⟨ refl ⟩
    ((Γ „ T ⟦ id ⟧ σ→ Γ „ T) ∋ id ∘ π “ (ξ !> _))
      ≅⟨ {!!} ⟩
    ((Γ „ T ⟦ id ⟧ σ→ Γ „ T) ∋ π “ (ξ !> {!cong (λ T' → Tm (Γ „ T') ) !}))
      ≅⟨ {!hap
           (hap
             (hap
               hrefl⟨ (λ T' π' ξ' → (Γ „ T' σ→ Γ „ T) ∋ π' “ ξ') ⟩
               ((T ⟦ id ⟧ ≅ T) ∋ ≡-to-≅ tysub-id))
             {!!})
           {!!}!}
       ⟩
         --hrefl⟨ {!λ T' π' ξ' → {!(Γ „ T' σ→ Γ „ T) ∋ π' “ ξ'!}!} ⟩
    ((Γ „ T σ→ Γ „ T) ∋ π “ ξ)
      ≅⟨ ≡-to-≅ π“ξ ⟩
    ((Γ „ T σ→ Γ „ T) ∋ id) h∎)
    {-
      where
        aux : (T' : Ty Γ) → (π' : Γ „ T' σ→ Γ) → .(T' ⟦ π ⟧ ≡ T ⟦ π' ⟧) → (Γ „ T' σ→ Γ „ T)
        aux T' π' p = π' “ (ξ !> cong (λ T'' → Tm (Γ „ T') T'') p)
        
        aux1 : aux (T ⟦ id ⟧) (id ∘ π) (sym tysub-comp) ≡ aux (T ⟦ id ⟧) π (cong (λ T' → T' ⟦ π ⟧) tysub-id)
        aux1 with id ∘ π{Γ}{T ⟦ id ⟧}
                | id ∘ π{Γ}{T ⟦ id ⟧} ≡ π ∋ lunit _
        aux1 | .π | refl = refl

        aux2 : aux (T ⟦ id ⟧) π (cong (λ T' → T' ⟦ π ⟧) tysub-id) ≅ aux T π refl
        aux2 with T ⟦ id ⟧
                | T ⟦ id ⟧ ≡ T ∋ tysub-id
                | π{Γ}{T ⟦ id ⟧}
                --| (T ⟦ id ⟧ ⟦ π{Γ}{T ⟦ id ⟧} ⟧ ≡ T ⟦ π ⟧) ∋ (cong (λ T' → T' ⟦ π ⟧) tysub-id)
        aux2 | T' | e | e' = {!!}
    -}
  hom-comp c-compr = {!!}
-}
