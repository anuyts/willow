{-# OPTIONS --type-in-type --rewriting --irrelevant-projections #-}

module willow2.cat.CwF.Product where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open import willow2.basic.HeterogeneousEquality public
open import willow2.cat.Product public
open import willow2.cat.CwF public

_ç×_ : CwF → CwF → CwF
cCtx (çA ç× çB) = cCtx çA c× cCtx çB
Ty (çA ç× çB) (Γ1 , Γ2) = Ty çA Γ1 × Ty çB Γ2
Tm (çA ç× çB) (Γ1 , Γ2) (T1 , T2) = Tm çA Γ1 T1 × Tm çB Γ2 T2
IsCwF.Tsub (isCwF (çA ç× çB)) (T1 , T2) (σ1 , σ2) = (T1 T[ σ1 ]) , (T2 T[ σ2 ])
IsCwF.T[id] (isCwF (çA ç× çB)) = ext-× T[id] T[id]
IsCwF.T[][] (isCwF (çA ç× çB)) = ext-× T[][] T[][]
IsCwF.tsub (isCwF (çA ç× çB)) (t1 , t2) (σ1 , σ2) = (t1 t[ σ1 ]) , (t2 t[ σ2 ])
IsCwF.t[id] (isCwF (çA ç× çB)) = hext-× t[id] t[id]
IsCwF.t[][] (isCwF (çA ç× çB)) = hext-× t[][] t[][]
IsCwF.Ω (isCwF (çA ç× çB)) = Ω , Ω
IsCwF.ω (isCwF (çA ç× çB)) = ω , ω
IsCwF.ext-Ω (isCwF (çA ç× çB)) = ext-× ext-Ω ext-Ω
IsCwF._„_ (isCwF (çA ç× çB)) (Γ1 , Γ2) (T1 , T2) = (Γ1 „ T1) , (Γ2 „ T2)
IsCwF.π (isCwF (çA ç× çB)) = π , π
IsCwF.ξ (isCwF (çA ç× çB)) = ξ , ξ
IsCwF._“_ (isCwF (çA ç× çB)) (σ1 , σ2) (t1 , t2) = (σ1 “ t1) , (σ2 “ t2)
IsCwF.π“ (isCwF (çA ç× çB)) = ext-× π“ π“
IsCwF.ξ“ (isCwF (çA ç× çB)) = hext-× ξ“ ξ“
IsCwF.π“ξ (isCwF (çA ç× çB)) {Δ1 , Δ2}{Γ1 , Γ2}{T1 , T2}{σ1 , σ2} = ext-×
  (begin
    σ1
      ≡⟨ π“ξ ⟩
    π ∘ σ1 “ (ξ t[ σ1 ] !> cong (Tm çA Δ1) T[][])
      ≡⟨ refl ⟩
    π ∘ σ1 “ proj₁ (ξ t[ σ1 ] !> cong (Tm çA Δ1) T[][] , tsub {{isCwF çB}} ξ σ2 !> cong (Tm çB Δ2) T[][])
      ≡⟨ cong (λ p → π ∘ σ1 “ proj₁ p) !>× ⟩
    π ∘ σ1 “ proj₁ ((ξ t[ σ1 ] , tsub {{isCwF çB}} ξ σ2) !> cong₂ _×_ (cong (Tm çA Δ1) T[][]) (cong (Tm çB Δ2) T[][])) ∎
  )
  (begin
    σ2
      ≡⟨ π“ξ ⟩
    π ∘ σ2 “ (ξ t[ σ2 ] !> cong (Tm çB Δ2) T[][])
      ≡⟨ refl ⟩
    π ∘ σ2 “ proj₂ (ξ t[ σ1 ] !> cong (Tm çA Δ1) T[][] , ξ t[ σ2 ] !> cong (Tm çB Δ2) T[][])
      ≡⟨ cong (λ p → π ∘ σ2 “ proj₂ p) !>× ⟩
    π ∘ σ2 “ proj₂ ((ξ t[ σ1 ] , ξ t[ σ2 ]) !> cong₂ _×_ (cong (Tm çA Δ1) T[][]) (cong (Tm çB Δ2) T[][])) ∎
  )


  {-≅-to-≡ (hext-×
    (hbegin
      σ1
        ≅⟨ ≡-to-≅ π“ξ ⟩
      π ∘ σ1 “ (ξ t[ σ1 ]) !> _
        ≅⟨ hcong (λ t → π ∘ σ1 “ t) (hbegin
            ξ t[ σ1 ] !> _
              ≅⟨ {!!} ⟩
            {!!}
              ≅⟨ {!!} ⟩
            {!!}
              ≅⟨ {!!} ⟩
            --tsub {Δ = Δ1} {Γ1 „ T1} {T1 T[ π ]} (ξ {Γ = Γ1} {T1}) σ1
            proj₁ (ξ t[ σ1 ] , ξ t[ σ2 ])
              ≅⟨ hcong proj₁ !>≅ ⟩
            proj₁ ((ξ t[ σ1 ] , ξ t[ σ2 ]) !> _) h∎
        ) ⟩
      π ∘ σ1 “ proj₁ ((ξ t[ σ1 ] , ξ t[ σ2 ]) !> _) h∎
    )
    {!proj₁!}
  )-}


    {-trans
      π“ξ
      (cong (λ t → π ∘ σ1 “ t) (≅-to-≡ (htrans
        {!!}
        (hcong proj₁ !>≅)
      )))
    -}
    --{!!}

