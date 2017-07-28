open import willow.cat.Category public
open import willow.basic.UIP.HeteroIdentity public
import willow.cat.CwF

module willow.cat.CwF.HasProducts {ℓctx ℓsub ℓty ℓtm : Level} (cwf : willow.cat.CwF.CwF ℓctx ℓsub ℓty ℓtm) where

open willow.cat.CwF.CwF cwf public

record HasProducts : Set (ℓctx ⊔ ℓsub ⊔ ℓty ⊔ ℓtm) where
  no-eta-equality
  field
    TΠ : {Γ : Ctx} → (A : Ty Γ) → (B : Ty (Γ „ A)) → Ty Γ
    TΠ[]' : {Δ Γ : Ctx} {σ : Sub Δ Γ} → (A : Ty Γ) → (B : Ty (Γ „ A))
      → (TΠ A B) T[ σ ] == TΠ (A T[ σ ]) (B T[ σcompr σ A ])

    tλ : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (b : Tm (Γ „ A) B) → Tm Γ (TΠ A B)
    tap : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (f : Tm Γ (TΠ A B)) → Tm (Γ „ A) B
    tλβ' : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (b : Tm (Γ „ A) B) → tap (tλ b) == b
    tλη' : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (f : Tm Γ (TΠ A B)) → tλ (tap f) == f
    
    tλ[]' : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (b : Tm (Γ „ A) B)
      → (tλ b) t[ σ ] === tλ (b t[ σcompr σ A ])

  TΠ[]* TΠ[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → (A : Ty Γ) → (B : Ty (Γ „ A))
      → (TΠ A B) T[ σ ] == TΠ (A T[ σ ]) (B T[ σcompr σ A ])
  abstract TΠ[]* = TΠ[]'
  TΠ[] A B = trust(TΠ[]* A B)

  tλβ* tλβ : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (b : Tm (Γ „ A) B) → tap (tλ b) == b
  abstract tλβ* = tλβ'
  tλβ b = trust (tλβ* b)

  tλη* tλη : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (f : Tm Γ (TΠ A B)) → tλ (tap f) == f
  abstract tλη* = tλη'
  tλη f = trust (tλη* f)

  tλ[]* tλ[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (b : Tm (Γ „ A) B)
      → (tλ b) t[ σ ] === tλ (b t[ σcompr σ A ])
  abstract tλ[]* = tλ[]'
  tλ[] b = htrust (tλ[]* b)

  tap[]' tap[] : {Δ Γ : Ctx} {σ : Sub Δ Γ} → {A : Ty Γ} → {B : Ty (Γ „ A)} → (f : Tm Γ (TΠ A B))
    → (tap f) t[ σcompr σ A ] == tap (tra! (map= (Tm Δ) (TΠ[] A B)) (f t[ σ ]))
  abstract
   tap[]' {Δ}{Γ}{σ}{A}{B} f = to-homog (
      via (tap f) t[ σcompr σ A ] $ hrefl h•
      via tap (tλ ((tap f) t[ σcompr σ A ])) $ to-heter (sym (tλβ ((tap f) t[ σcompr σ A ]))) h•
      via tap (tra! (map= (Tm Δ) (TΠ[] A B)) ((tλ (tap f)) t[ σ ])) $ hdmap= tap (
          to-homog (hsym (tλ[] (tap f)) h• hsym (hhapply (htra! (map= (Tm Δ) (TΠ[] A B))) (tλ (tap f) t[ σ ])))
        ) h•
      to-heter (map= (λ f' → tap (tra! (map= (Tm Δ) (TΠ[] A B)) (f' t[ σ ]))) (tλη f))
    )
  tap[] f = trust (tap[]' f)
