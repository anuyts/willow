open import willow.cat.Category public
open import willow.basic.UIP.HeteroIdentity public
import willow.cat.CwF

module willow.cat.CwF.HasUniverse {ℓctx ℓsub ℓty ℓtm : Level} (cwf : willow.cat.CwF.CwF ℓctx ℓsub ℓty ℓtm) where

open willow.cat.CwF.CwF cwf public

record HasUniverse : Set (ℓctx ⊔ ℓsub ⊔ ℓty ⊔ ℓtm) where
  no-eta-equality
  field
    TUni : {Γ : Ctx} → Ty Γ
    TUni[]' : {Δ Γ : Ctx} {σ : Sub Δ Γ} → TUni T[ σ ] == TUni

  TUni[]* : {Δ Γ : Ctx} {σ : Sub Δ Γ} → TUni T[ σ ] == TUni
  abstract TUni[]* = TUni[]'
  TUni[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → TUni T[ σ ] == TUni
  TUni[] {Δ}{Γ}{σ} = trust TUni[]*

  field
    TEl : {Γ : Ctx} → (tA : Tm Γ TUni) → Ty Γ

    tclassify : {Γ : Ctx} → (A : Ty Γ) → Tm Γ TUni
    uni-id' : {Γ : Ctx} → (tA : Tm Γ TUni) → tclassify (TEl tA) == tA
    type-id' : {Γ : Ctx} → (A : Ty Γ) → TEl (tclassify A) == A

    tclassify[]' : {Δ Γ : Ctx} {σ : Sub Δ Γ} → (A : Ty Γ) → tclassify A t[ σ ] === tclassify (A T[ σ ])

  uni-id* uni-id : {Γ : Ctx} → (tA : Tm Γ TUni) → tclassify (TEl tA) == tA
  abstract uni-id* = uni-id'
  uni-id tA = trust (uni-id* tA)

  type-id* type-id : {Γ : Ctx} → (A : Ty Γ) → TEl (tclassify A) == A
  abstract type-id* = type-id'
  type-id A = trust (type-id* A)

  tclassify[]* tclassify[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → (A : Ty Γ) → tclassify A t[ σ ] === tclassify (A T[ σ ])
  abstract tclassify[]* = tclassify[]'
  tclassify[] A = htrust (tclassify[]* A)
  
  TEl[]' TEl[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → (tA : Tm Γ TUni)
    → TEl tA T[ σ ] == TEl (tra! (trust (map= (Tm Δ) TUni[])) (tA t[ σ ]))
  abstract
    TEl[]' {Δ}{Γ}{σ} tA = to-homog (
        via TEl tA T[ σ ] $ hrefl h•
        via TEl {Δ} (tclassify (TEl tA T[ σ ])) $ to-heter (sym (type-id (TEl tA T[ σ ]))) h•
        via TEl {Δ} (tra! (trust (map= (Tm Δ) TUni[])) (tclassify (TEl tA) t[ σ ])) $
          hdmap= (TEl {Δ}) (to-homog (hsym (tclassify[] (TEl tA)) h• hsym (hhapply (htra! (trust (map= (Tm Δ) TUni[]))) _))) h•
        hdmap= (λ tA' → TEl (tra! (trust (map= (Tm Δ) TUni[])) (tA' t[ σ ]))) (uni-id tA)
      )
  TEl[] tA = trust (TEl[]' tA)
