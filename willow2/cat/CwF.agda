{-# OPTIONS --type-in-type --rewriting #-}

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
