{-# OPTIONS --type-in-type --rewriting --irrelevant-projections #-}

module willow2.cat.CwF.HasSigma where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open import willow2.basic.HeterogeneousEquality public
open import willow2.cat.Product public
open import willow2.cat.CwF public

record HasSigma (ç : CwF) : Set where
  no-eta-equality
  field
    TΣ : {Γ : Ctx ç} → (A : Ty ç Γ) → (B : Ty ç (Γ „ A)) → Ty ç Γ
    TΣ[] : {Δ Γ : Ctx ç} {σ : Sub ç Δ Γ} → {A : Ty ç Γ} → {B : Ty ç (Γ „ A)}
      → (TΣ A B) T[ σ ] ≡ TΣ (A T[ σ ]) (B T[ σ ⊕ ])
    tpair : {Γ : Ctx ç} {A : Ty ç Γ} {B : Ty ç (Γ „ A)}
            (a : Tm ç Γ A) (b : Tm ç Γ (B T[ ξ:= a ])) → Tm ç Γ (TΣ A B)
    tfst : {Γ : Ctx ç} {A : Ty ç Γ} {B : Ty ç (Γ „ A)} (p : Tm ç Γ (TΣ A B)) → Tm ç Γ A
    tsnd : {Γ : Ctx ç} {A : Ty ç Γ} {B : Ty ç (Γ „ A)} (p : Tm ç Γ (TΣ A B)) → Tm ç Γ (B T[ ξ:= tfst p ])
    tfstβ : {Γ : Ctx ç} {A : Ty ç Γ} {B : Ty ç (Γ „ A)}
            (a : Tm ç Γ A) (b : Tm ç Γ (B T[ ξ:= a ])) → tfst (tpair a b) ≡ a
    tsndβ : {Γ : Ctx ç} {A : Ty ç Γ} {B : Ty ç (Γ „ A)}
            (a : Tm ç Γ A) (b : Tm ç Γ (B T[ ξ:= a ])) → tsnd (tpair a b) ≅ b
    tpairη : {Γ : Ctx ç} {A : Ty ç Γ} {B : Ty ç (Γ „ A)} {p : Tm ç Γ (TΣ A B)}
            → tpair (tfst p) (tsnd p) ≡ p
    tfst[] : {Δ Γ : Ctx ç} {σ : Sub ç Δ Γ} {A : Ty ç Γ} {B : Ty ç (Γ „ A)} (p : Tm ç Γ (TΣ A B))
            → tfst p t[ σ ] ≡ tfst (p t[ σ ] !> cong (Tm ç Δ) TΣ[])
    tsnd[] : {Δ Γ : Ctx ç} {σ : Sub ç Δ Γ} {A : Ty ç Γ} {B : Ty ç (Γ „ A)} (p : Tm ç Γ (TΣ A B))
            → tsnd p t[ σ ] ≅ tsnd (p t[ σ ] !> cong (Tm ç Δ) TΣ[])

  tpair[] : {Δ Γ : Ctx ç} {σ : Sub ç Δ Γ} {A : Ty ç Γ} {B : Ty ç (Γ „ A)}
            (a : Tm ç Γ A) (b : Tm ç Γ (B T[ ξ:= a ]))
            → tpair a b t[ σ ] ≅
               tpair (a t[ σ ]) (b t[ σ ] !> cong (Tm ç Δ) (
                 trans T[][] (trans
                   (cong (λ σ' → B T[ σ' ]) ξ:=comp)
                   (sym T[][])
                 )
               ))
  tpair[] {Δ}{Γ}{σ}{A}{B} a b = hbegin
    tpair a b t[ σ ]
      ≅⟨ {!hsym tpairη!} ⟩
    {!!} -- and so on bu ttype-checking is too slow.
      ≅⟨ {!!} ⟩
    {!!}
      ≅⟨ {!!} ⟩
    {!!}
      ≅⟨ {!!} ⟩
    {!!} h∎
