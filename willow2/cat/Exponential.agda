{-# OPTIONS --type-in-type --irrelevant-projections #-}

module willow2.cat.Exponential where

open import willow2.cat.Category
open import willow2.cat.Product
open import willow2.basic.Funext

cExp : Cat → Cat → Cat
ℓo (cExp cA cB) = ℓo cA ⊔ ℓh cA ⊔ ℓo cB ⊔ ℓh cB
ℓh (cExp cA cB) = ℓ?
Obj (cExp cA cB) = cA c→ cB
Hom (cExp cA cB) cf cg = cf nt→ cg
IsCat.id⟨_⟩ (isCat (cExp cA cB)) cf = nt-id
IsCat._∘_ (isCat (cExp cA cB)) ntb nta = ntb nt∘ nta
IsCat.assoc (isCat (cExp cA cB)) ntc ntb nta = ext-nt (λ= a , assoc _ _ _)
IsCat.lunit (isCat (cExp cA cB)) nta = ext-nt (λ= a , lunit _)
IsCat.runit (isCat (cExp cA cB)) nta = ext-nt (λ= a , runit _)

c-comp : ∀{cA cB cC} → ((cExp cB cC) c× (cExp cA cB) c→ cExp cA cC)
obj (c-comp {cA} {cB} {cC}) (cg , cf) = cg c∘ cf
hom (c-comp {cA} {cB} {cC}) {cg1 , cf1}{cg2 , cf2} (ntg , ntf) = ntg nt⊚ ntf
hom-id (c-comp {cA} {cB} {cC}) {cg , cf} = ext-nt (λ= a , (begin
  id ∘ hom cg id
    ≡⟨ lunit (hom cg id) ⟩
  hom cg id
    ≡⟨ hom-id cg ⟩
  id ∎))
{- Hom-comp proves that the upper right path (LHS) is equal to the lower left path (RHS).
   Additionally, in the LHS, the horizontal part is completely under g1.
   We also have to move parentheses.
   g1 f1 a  →[ g1 ntf a ]→  g1 f2 a  →[ g1 ntf' a ]→  g1 f3 a

                                  ↓                           ↓
                            [ ntg f2 a ]                [ ntg f3 a ]
                                  ↓                           ↓

                              g2 f2 a  →[ g2 ntf' a ]→  g2 f3 a

                                                              ↓
                                                        [ntg' f3 a ]
                                                              ↓

                                                          g3 f3 a
-}
hom-comp (c-comp {cA} {cB} {cC}) {cg1 , cf1}{cg2 , cf2}{cg3 , cf3} {ntg' , ntf'}{ntg , ntf} = ext-nt (λ= a , (begin
  (obj ntg' (obj cf3 a) ∘ obj ntg (obj cf3 a)) ∘ hom cg1 (obj ntf' a ∘ obj ntf a)
    ≡⟨ cong (λ (ψ : Hom cC _ _) → _ ∘ ψ) (hom-comp cg1) ⟩
  (obj ntg' (obj cf3 a) ∘ obj ntg (obj cf3 a)) ∘ (hom cg1 (obj ntf' a) ∘ hom cg1 (obj ntf a))
    ≡⟨ assoc _ _ _ ⟩
  obj ntg' (obj cf3 a) ∘ (obj ntg (obj cf3 a) ∘ (hom cg1 (obj ntf' a) ∘ hom cg1 (obj ntf a)))
    ≡⟨ cong (λ (ψ : Hom cC _ _) → _ ∘ ψ) (sym (assoc _ _ _)) ⟩
  obj ntg' (obj cf3 a) ∘ ((obj ntg (obj cf3 a) ∘ hom cg1 (obj ntf' a)) ∘ hom cg1 (obj ntf a))
    ≡⟨ cong (λ (ψ : Hom cC _ _) → _ ∘ (ψ ∘ _)) (sym (nat ntg {φ = obj ntf' a})) ⟩
  obj ntg' (obj cf3 a) ∘ ((hom cg2 (obj ntf' a) ∘ obj ntg (obj cf2 a)) ∘ hom cg1 (obj ntf a))
    ≡⟨ cong (λ (ψ : Hom cC _ _) → _ ∘ ψ) (assoc _ _ _) ⟩
  obj ntg' (obj cf3 a) ∘ (hom cg2 (obj ntf' a) ∘ (obj ntg (obj cf2 a) ∘ hom cg1 (obj ntf a)))
    ≡⟨ sym (assoc _ _ _) ⟩
  (obj ntg' (obj cf3 a) ∘ hom cg2 (obj ntf' a)) ∘ (obj ntg (obj cf2 a) ∘ hom cg1 (obj ntf a)) ∎))
