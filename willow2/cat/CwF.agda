{-# OPTIONS --type-in-type --rewriting #-}

module willow2.cat.CwF where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open import willow2.basic.HeterogeneousEquality public
open Terminal public

--TODO: split up into CwF and IsCwF
{-# BUILTIN REWRITE _≡_ #-}

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
  {-# REWRITE tysub-id' #-}

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
