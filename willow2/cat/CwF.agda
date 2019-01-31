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

record IsCwF (cCtx : Cat) {Ty : (Obj cCtx) → Set} (Tm : (Γ : (Obj cCtx)) → Ty Γ → Set) : Set where
  field
    --{{isCat}} : IsCat (Hom cCtx)
    Tsub : ∀ {Δ Γ : (Obj cCtx)} (T : Ty Γ) → (Hom cCtx Δ Γ) → Ty Δ
    .T[id] : ∀ {Γ : (Obj cCtx)} {T : Ty Γ} → Tsub T id ≡ T
    .T[][] : ∀ {Θ Δ Γ : (Obj cCtx)} {τ : Hom cCtx Θ Δ} {σ : Hom cCtx Δ Γ} {T : Ty Γ} → Tsub (Tsub T σ) τ ≡ Tsub T (σ ∘ τ)
    tsub : ∀{Δ Γ : (Obj cCtx)} {T : Ty Γ} → Tm Γ T → (σ : Hom cCtx Δ Γ) → Tm Δ (Tsub T σ)
    .t[id] : ∀{Γ : (Obj cCtx)} {T : Ty Γ} {t : Tm Γ T} → (tsub t id ≅ t)
    .t[][] : ∀ {Θ Δ Γ : (Obj cCtx)} {τ : Hom cCtx Θ Δ} {σ : Hom cCtx Δ Γ} {T : Ty Γ} {t : Tm Γ T} → tsub (tsub t σ) τ ≅ tsub t (σ ∘ τ)
    Ω : (Obj cCtx)
    ω : {Γ : (Obj cCtx)} → Hom cCtx Γ Ω
    ext-Ω : {Γ : (Obj cCtx)} {σ : Hom cCtx Γ Ω} → σ ≡ ω
    _„_ : (Γ : (Obj cCtx)) → Ty Γ → (Obj cCtx)
    π : {Γ : (Obj cCtx)} {T : Ty Γ} → Hom cCtx (Γ „ T) Γ
    ξ : {Γ : (Obj cCtx)} {T : Ty Γ} → Tm (Γ „ T) (Tsub T π)
    _“_ : {Δ Γ : (Obj cCtx)} {T : Ty Γ} (σ : Hom cCtx Δ Γ) (t : Tm Δ (Tsub T σ)) → Hom cCtx Δ (Γ „ T)
    .π“ : {Δ Γ : (Obj cCtx)} {T : Ty Γ} {σ : Hom cCtx Δ Γ} {t : Tm Δ (Tsub T σ)}
            → π ∘ (σ “ t) ≡ σ
    .ξ“ : {Δ Γ : (Obj cCtx)} {T : Ty Γ} {σ : Hom cCtx Δ Γ} {t : Tm Δ (Tsub T σ)}
            → tsub ξ (σ “ t) ≅ t
    .π“ξ : {Γ : (Obj cCtx)} {T : Ty Γ} → id⟨ Γ „ T ⟩ ≡ π “ ξ

  _T[_] = Tsub
  _t[_] = tsub

  Ctx : Set
  Ctx = (Obj cCtx)
open IsCwF {{...}} public

record CwF : Set where
  constructor cwf
  field
    cCtx : Cat
    {Ty} : (Obj cCtx) → Set
    Tm : (Γ : (Obj cCtx)) → Ty Γ → Set
    {{isCwF}} : IsCwF cCtx Tm

  c-ty : cOp cCtx c→ cSet _
  obj c-ty = Ty
  hom c-ty {Γ}{Δ} σ T = T T[ σ ]
  hom-id c-ty {Γ} = λ= T , T[id]
  hom-comp c-ty {Γ}{Δ}{Θ} τ σ = λ= T , sym T[][]

  c-fam : cOp cCtx c→ cFam
  obj c-fam Γ = (Ty Γ) , (Tm Γ)
  hom c-fam {Γ}{Δ} σ = (λ T → T T[ σ ]) , λ T t → t t[ σ ]
  hom-id c-fam {Γ} = ext-Σ (λ= T , T[id]) (λ≅ T , λ≅ t , t[id])
  hom-comp c-fam {Θ}{Δ}{Γ} σ τ = ext-Σ (λ= T , sym T[][]) (λ≅ T , λ≅ t , hsym t[][])
open CwF public

{-

-- Operators necessary for cCtx to be a CwF
record IsCwF (cCtx : Cat) : Set where
  field
    c-ty : cOp cCtx c→ cSet _
    c-tm : cOp (c∫⁻ cCtx c-ty) c→ cSet _
    Ω : Obj cCtx
    ω : {Γ : Obj cCtx} → Hom cCtx Γ Ω
    ext-Ω : {Γ : Obj cCtx} {σ : Hom cCtx Γ Ω} → σ ≡ ω
    _„_ : (Γ : Obj cCtx) → obj c-ty Γ → Obj cCtx
    π : {Γ : Obj cCtx} {T : obj c-ty Γ} → Hom cCtx (Γ „ T) Γ
    ξ : {Γ : Obj cCtx} {T : obj c-ty Γ} → obj c-tm ((Γ „ T) , hom c-ty π T)
    _“_ : {Δ Γ : Obj cCtx} {T : obj c-ty Γ} (σ : Hom cCtx Δ Γ) (t : obj c-tm (Δ , hom c-ty σ T))
            → Hom cCtx Δ (Γ „ T)
    .π“ : {Δ Γ : Obj cCtx} {T : obj c-ty Γ} {σ : Hom cCtx Δ Γ} {t : obj c-tm (Δ , hom c-ty σ T)}
            → π ∘ (σ “ t) ≡ σ
    .ξ“ : {Δ Γ : Obj cCtx} {T : obj c-ty Γ} {σ : Hom cCtx Δ Γ} {t : obj c-tm (Δ , hom c-ty σ T)}
            → hom c-tm (σ “ t , refl) ξ ≅ t
    .π“ξ : {Γ : Obj cCtx} {T : obj c-ty Γ} → id⟨ Γ „ T ⟩ ≡ π “ ξ
open IsCwF public

-- A CwF is a category of contexts that is a CwF :)
record CwF : Set where
  constructor cwf
  field
    cCtx : Cat
    {{isCwF}} : IsCwF cCtx
open CwF public

-- Some practical operations on CwFs.
module CwF-ops (cwf : CwF) where
  ops = isCwF cwf

  Ctx : Set
  Ctx = Obj (cCtx cwf)

  Sub : Ctx → Ctx → Set
  Sub = Hom (cCtx cwf)

  Ty : Ctx → Set
  Ty Γ = obj (c-ty ops) Γ

  Tm : (Γ : Ctx) (T : Ty Γ) → Set
  Tm Γ T = obj (c-tm ops) (Γ , T)
  
  _T[_] : ∀ {Δ Γ : Ctx} (T : Ty Γ) → (Sub Δ Γ) → Ty Δ
  T T[ σ ] = hom (c-ty ops) σ T

  .T[id] : ∀ {Γ : Ctx} {T : Ty Γ} → T T[ id ] ≡ T
  T[id] {Γ}{T} = cong-app (hom-id (c-ty ops)) T
  .T[][] : ∀ {Θ Δ Γ : Ctx} {τ : Sub Θ Δ} {σ : Sub Δ Γ} {T : Ty Γ} → T T[ σ ] T[ τ ] ≡ T T[ σ ∘ τ ]
  T[][] {Θ}{Δ}{Γ}{τ}{σ}{T} = cong-app (sym (hom-comp (c-ty ops) τ σ)) T

  _t[_] : ∀{Δ Γ : Ctx} {T : Ty Γ} → Tm Γ T → (σ : Sub Δ Γ) → Tm Δ (T T[ σ ])
  t t[ σ ] = hom (c-tm ops) (σ , refl) t

  .t[id] : ∀{Γ : Ctx} {T : Ty Γ} {t : Tm Γ T} → (t t[ id ] ≅ t)
  t[id] {Γ}{T}{t} = hbegin
        hom (c-tm ops) (id , refl) t
          ≅⟨ hcong₂
              (λ (T' : Ty Γ) (id,- : [ φ ∈ Sub Γ Γ ! T T[ φ ] ≡ T' ]) → hom (c-tm ops) id,- t)
              (≡-to-≅ T[id])
              (hext-Subset refl (λ≅ φ ,
                 hcong (λ T' → T T[ φ ] ≡ T') (≡-to-≅ T[id])
              )) ⟩
        hom (c-tm ops) (id , T[id]) t
          ≅⟨ ≡-to-≅ (cong-app (hom-id (c-tm ops)) t) ⟩
        t h∎

  .t[][] : ∀ {Θ Δ Γ : Ctx} {τ : Sub Θ Δ} {σ : Sub Δ Γ} {T : Ty Γ} {t : Tm Γ T} → t t[ σ ] t[ τ ] ≅ t t[ σ ∘ τ ]
  t[][] {Θ}{Δ}{Γ}{τ}{σ}{T}{t} = hbegin
    (t t[ σ ] t[ τ ])
      ≅⟨ refl ⟩
    hom (c-tm ops) (τ , refl) (hom (c-tm ops) (σ , refl) t)
      ≅⟨ ≡-to-≅ (sym (cong-app (hom-comp (c-tm ops) (τ , refl) (σ , refl)) t)) ⟩
    hom (c-tm ops) (σ ∘ τ , sym T[][]) t
      ≅⟨ hcong₂
           (λ (T' : Ty Θ) (σ∘τ,- : [ φ ∈ Sub Θ Γ ! T T[ φ ] ≡ T' ]) → hom (c-tm ops) σ∘τ,- t)
           (≡-to-≅ T[][])
           (hext-Subset refl (λ≅ φ ,
              hcong (λ T' → T T[ φ ] ≡ T') (≡-to-≅ T[][])
           )) ⟩
    hom (c-tm ops) (σ ∘ τ , refl) t
      ≅⟨ refl ⟩
    (t t[ σ ∘ τ ]) h∎

  c-fam : cOp (cCtx cwf) c→ cFam
  obj c-fam Γ = (Ty Γ) , (Tm Γ)
  hom c-fam {Γ}{Δ} σ = (λ T → T T[ σ ]) , λ T t → t t[ σ ]
  hom-id c-fam {Γ} = ext-Σ (λ= T , T[id]) (λ≅ T , λ≅ t , t[id])
  hom-comp c-fam {Θ}{Δ}{Γ} σ τ = ext-Σ (λ= T , sym T[][]) (λ≅ T , λ≅ t , hsym t[][])
-}










{-
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
-}
