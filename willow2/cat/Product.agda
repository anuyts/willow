{-# OPTIONS --type-in-type --irrelevant-projections #-}

module willow2.cat.Product where

open import willow2.cat.Category public
open import Data.Product public
open import willow2.basic.PropositionalEquality

_c×_ : Cat → Cat → Cat
ℓo (cA c× cB) = ℓo cA ⊔ ℓo cB
ℓh (cA c× cB) = ℓh cA ⊔ ℓh cB
Obj (cA c× cB) = Obj cA × Obj cB
Hom (cA c× cB) (a1 , b1) (a2 , b2) = Hom cA a1 a2 × Hom cB b1 b2
IsCat.id⟨_⟩ (isCat (cA c× cB)) x = id , id
IsCat._∘_ (isCat (cA c× cB)) (α2 , β2) (α1 , β1) = (α2 ∘ α1) , (β2 ∘ β1)
IsCat.assoc (isCat (cA c× cB)) ψ ξ φ = ext-× (assoc _ _ _) (assoc _ _ _)
IsCat.lunit (isCat (cA c× cB)) φ = ext-× (lunit _) (lunit _)
IsCat.runit (isCat (cA c× cB)) φ = ext-× (runit _) (runit _)

c-proj₁ : ∀{cA cB} → (cA c× cB c→ cA)
c-proj₁ = ftr proj₁

c-proj₂ : ∀{cA cB} → (cA c× cB c→ cB)
c-proj₂ = ftr proj₂

_c,_ : ∀{cA cB cC} (cf : cA c→ cB) (cg : cA c→ cC) → (cA c→ cB c× cC)
obj (cf c, cg) = _
hom (cf c, cg) φ = hom cf φ , hom cg φ
hom-id (cf c, cg) = ext-× (hom-id cf) (hom-id cg)
hom-comp (cf c, cg) ψ φ = ext-× (hom-comp cf _ _) (hom-comp cg _ _)
