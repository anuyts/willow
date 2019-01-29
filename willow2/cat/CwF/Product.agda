{-# OPTIONS --type-in-type --rewriting --irrelevant-projections #-}

module willow2.cat.CwF.Product where

open import willow2.cat.Category
open import willow2.cat.OfElements public
open import willow2.cat.Limit.Local
open import willow2.basic.HeterogeneousEquality public
open import willow2.cat.Product public
open import willow2.cat.CwF public

_ç×_ : CwF → CwF → CwF
Ctx (çA ç× çB) = Obj (cCtx çA c× cCtx çB)
Sub (çA ç× çB) = Hom (cCtx çA c× cCtx çB)
Ty (çA ç× çB) (Γ1 , Γ2) = Ty çA Γ1 × Ty çB Γ2
Tm (çA ç× çB) (Γ1 , Γ2) (T1 , T2) = Tm çA Γ1 T1 × Tm çB Γ2 T2
IsCwF.isCat (isCwF (çA ç× çB)) = isCat (cCtx çA c× cCtx çB)
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
IsCwF.π“ξ (isCwF (çA ç× çB)) = ext-× π“ξ π“ξ


