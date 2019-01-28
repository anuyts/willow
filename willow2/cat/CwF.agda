{-# OPTIONS --type-in-type --rewriting --irrelevant-projections #-}

module willow2.cat.CwF where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open import willow2.basic.HeterogeneousEquality public

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

record OpsCtx (Ctx : Set) : Set where
  field
    ‚ : Ctx
open OpsCtx {{...}} public

record OpsSub {Ctx : Set} {{opsCtx : OpsCtx Ctx}} (Sub : Ctx → Ctx → Set) : Set where
  field
    {{isCat}} : IsCat Sub
    ‘ : ∀{Γ} → Sub Γ ‚
    .ext-‚ : ∀{Γ} {σ : Sub Γ ‚} → σ ≡ ‘
open OpsSub {{...}} public

record OpsTy {Ctx : Set} {{opsCtx : OpsCtx Ctx}} (Ty : Ctx → Set) : Set where
  field
    _„_ : (Γ : Ctx) → Ty Γ → Ctx

  infix 10 _„_

open OpsTy {{...}} public

record OpsSubTy {Ctx : Set} {{opsCtx : OpsCtx Ctx}}
                (Sub : Ctx → Ctx → Set) {{opsSub : OpsSub Sub}}
                (Ty : Ctx → Set) {{opsTy : OpsTy Ty}} : Set where
  field
    _⊢_⟦_⟧ : ∀ (Δ : Ctx) {Γ} → Ty Γ → (σ : Sub Δ Γ) → Ty Δ
    .tysub-id : ∀{Γ} {T : Ty Γ} → Γ ⊢ T ⟦ id ⟧ ≡ T
    .tysub-comp : ∀{Θ Δ Γ} {T : Ty Γ} (σ : Sub Δ Γ) (τ : Sub Θ Δ) → Θ ⊢ T ⟦ σ ∘ τ ⟧ ≡ Θ ⊢ (Δ ⊢ T ⟦ σ ⟧) ⟦ τ ⟧
    π : ∀{Γ} {T : Ty Γ} → Sub (Γ „ T) Γ
    
  _⟦_⟧ : ∀ {Δ Γ} → Ty Γ → (σ : Sub Δ Γ) → Ty Δ
  T ⟦ σ ⟧ = _ ⊢ T ⟦ σ ⟧

  π⟨_⟩⟨_⟩ : ∀(Γ : Ctx) (T : Ty Γ) → Sub (Γ „ T) Γ
  π⟨ _ ⟩⟨ _ ⟩ = π

  infix 20 _⟦_⟧
  infix 5 _⊢_⟦_⟧
open OpsSubTy {{...}} public

record OpsTm {Ctx : Set} {{opsCtx : OpsCtx Ctx}}
                (Sub : Ctx → Ctx → Set) {{opsSub : OpsSub Sub}}
                (Ty : Ctx → Set) {{opsTy : OpsTy Ty}}
                {{opsSubTy : OpsSubTy Sub Ty}}
                (Tm : (Γ : Ctx) → Ty Γ → Set) : Set where
  field
    _⊢_[_] : ∀ (Δ : Ctx) {Γ} {T : Ty Γ} (t : Tm Γ T) → (σ : Sub Δ Γ) → Tm Δ (Δ ⊢ T ⟦ σ ⟧)
    .tmsub-id : ∀{Γ} {T : Ty Γ} {t : Tm Γ T} → Γ ⊢ t [ id ] ≅ t
    .tmsub-comp : ∀{Θ Δ Γ} {T : Ty Γ} {t : Tm Γ T} (σ : Sub Δ Γ) (τ : Sub Θ Δ) → Θ ⊢ t [ σ ∘ τ ] ≅ Θ ⊢ (Δ ⊢ t [ σ ]) [ τ ]
    _“_ : ∀{Δ Γ} {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (Δ ⊢ T ⟦ σ ⟧)) → Sub Δ (Γ „ T)
    ξ : ∀{Γ : Ctx} {T : Ty Γ} → Tm (Γ „ T) (Γ „ T ⊢ T ⟦ Sub _ Γ ∋ π{Γ = Γ}{T} ⟧)
    .{{π∘“}} : ∀{Δ Γ} {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (Δ ⊢ T ⟦ σ ⟧)) → π⟨ Γ ⟩⟨ T ⟩ ∘ (σ “ t) ≡ σ
    .{{ξ[“]}} : ∀{Δ Γ} {T : Ty Γ} → (σ : Sub Δ Γ) → (t : Tm Δ (Δ ⊢ T ⟦ σ ⟧)) → Δ ⊢ ξ [ σ “ t ] ≅ t
    .{{ext-„}} : ∀{Δ Γ} {T : Ty Γ} → {σ τ : Sub Δ (Γ „ T)}
      → π⟨ Γ ⟩⟨ T ⟩ ∘ σ ≡ π⟨ Γ ⟩⟨ T ⟩ ∘ τ → (Δ ⊢ ξ [ σ ]) ≅ (Δ ⊢ ξ [ τ ]) → σ ≡ τ
    
  _[_] : ∀ {Δ Γ} {T : Ty Γ} (t : Tm Γ T) → (σ : Sub Δ Γ) → Tm Δ (Δ ⊢ T ⟦ σ ⟧)
  t [ σ ] = _ ⊢ t [ σ ]
  _∋:_[_] : ∀ {Δ Γ} (T : Ty Γ) (t : Tm Γ T) → (σ : Sub Δ Γ) → Tm Δ (Δ ⊢ T ⟦ σ ⟧)
  T ∋: t [ σ ] = t [ σ ]
  _⊢_∋:_[_] : ∀ (Δ : Ctx) {Γ} (T : Ty Γ) (t : Tm Γ T) → (σ : Sub Δ Γ) → Tm Δ (Δ ⊢ T ⟦ σ ⟧)
  Δ ⊢ T ∋: t [ σ ] = t [ σ ]
  
  infix 20 _[_]
  infix 10 _“_
  infix 5 _⊢_[_]
open OpsTm {{...}} public

record CwF : Set where
  constructor cwf
  field
    Ctx : Set
    Sub : Ctx → Ctx → Set
    Ty : Ctx → Set
    Tm : (Γ : Ctx) → Ty Γ → Set
    {{opsCtx}} : OpsCtx Ctx
    {{opsSub}} : OpsSub Sub
    {{opsTy}} : OpsTy Ty
    {{opsSubTy}} : OpsSubTy Sub Ty
    {{opsTm}} : OpsTm Sub Ty Tm
    
  cCtx : Cat
  cCtx = cat Sub

  c-fam : cOp cCtx c→ cFam
  obj c-fam Γ = (Ty Γ) , (Tm Γ)
  hom c-fam {Γ}{Δ} σ = (λ T → Δ ⊢ T ⟦ σ ⟧) , (λ T t → Δ ⊢ T ∋: t [ σ ])
  hom-id c-fam = ext-Σ (λ= T , tysub-id) (λ≅ T , λ≅ t , tmsub-id)
  hom-comp c-fam σ τ = {!ext-Σ (λ= T , tysub-comp _ _) (λ≅ T , λ≅ t , tmsub-comp _ _)!}

{-

    
open CwF public

record CwFmorphism (çA çB : CwF) : Set where
  --field
    --ctx : Ctx çA → Ctx çB
    --sub : ∀{Δ Γ : Ctx çA} → Sub çA Δ Γ → Sub çB (ctx Δ) (ctx Γ)
    --ctx : cCtx c→ cCtx
-}
