open import willow.cat.Category public
open import willow.basic.UIP.HeteroIdentity public
import willow.cat.CwF

module willow.cat.CwF.HasSums {ℓctx ℓsub ℓty ℓtm : Level} (cwf : willow.cat.CwF.CwF ℓctx ℓsub ℓty ℓtm) where

open willow.cat.CwF.CwF cwf public

record HasProducts : Set (ℓctx ⊔ ℓsub ⊔ ℓty ⊔ ℓtm) where
  no-eta-equality
  field
    TΣ : {Γ : Ctx} → (A : Ty Γ) → (B : Ty (Γ „ A)) → Ty Γ
    TΣ[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → (A : Ty Γ) → (B : Ty (Γ „ A))
      → (TΣ A B) T[ σ ] == TΣ (A T[ σ ]) (B T[ σcompr σ A ])

    tpair : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (a : Tm Γ A) → (b : Tm Γ (B T[ σeval a ])) → Tm Γ (TΣ A B)
    tprl : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (ab : Tm Γ (TΣ A B)) → Tm Γ A
    tprr : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (ab : Tm Γ (TΣ A B)) → Tm Γ (B T[ σeval (tprl ab) ])

    tprlβ : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (a : Tm Γ A) → (b : Tm Γ (B T[ σeval a ]))
      → (tprl (tpair a b)) == a
    tprrβ : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (a : Tm Γ A) → (b : Tm Γ (B T[ σeval a ]))
      → (tprr (tpair a b)) === b
    tpairη : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (ab : Tm Γ (TΣ A B))
      → tpair (tprl ab) (tprr ab) == ab

    tpair[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (a : Tm Γ A) → (b : Tm Γ (B T[ σeval a ]))
      → (tpair a b) t[ σ ] === tpair (a t[ σ ]) (tra! (trust (map= (Tm Δ) (
        sym T[][] • map= (λ σ' → B T[ σ' ]) σeval[] • T[][]
      ))) (b t[ σ ]))
    tprl[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (ab : Tm Γ (TΣ A B))
      → (tprl ab) t[ σ ] == tprl (tra! (trust (map= (Tm Δ) (TΣ[] A B))) (ab t[ σ ]))
    tprr[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (ab : Tm Γ (TΣ A B))
      → (tprr ab) t[ σ ] === tprr (tra! (trust (map= (Tm Δ) (TΣ[] A B))) (ab t[ σ ]))
