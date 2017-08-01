{-# OPTIONS --type-in-type #-}

module willow2.cat.CwF where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open Terminal public

--TODO: split up into CwF and IsCwF

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

  Ty : (Γ : Ctx) → Set _
  Ty Γ = obj c-ty Γ

  _⟦_⟧ : ∀{Δ Γ} (T : Ty Γ) (σ : Δ σ→ Γ) → Ty Δ
  T ⟦ σ ⟧ = hom c-ty σ T
  .sub-id : ∀{Γ} {T : Ty Γ} → T ⟦ id ⟧ ≡ T
  sub-id {Γ}{T} = cong-app (hom-id c-ty) T
  .sub-comp : ∀{Θ Δ Γ} {τ : Θ σ→ Δ} {σ : Δ σ→ Γ} {T : Ty Γ} → T ⟦ σ ∘ τ ⟧ ≡ T ⟦ σ ⟧ ⟦ τ ⟧
  sub-comp = cong-app (hom-comp c-ty _ _) _

  
