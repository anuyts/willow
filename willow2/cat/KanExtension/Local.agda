{-# OPTIONS --type-in-type #-}

module willow2.cat.KanExtension.Local where

open import willow2.cat.Category
open import willow2.cat.Adjunction.Local public

record _=LeftKanExt_along_ {cT cA cB} (ck : cA c→ cB) (cf : cT c→ cB) (cp : cT c→ cA) : Set ℓ? where
  field
    pf-left-kan-ext : [ cf ↦ ck ]⊣ (c-comp c∘ (c-id c, c-const⟨ cExp cA cB ⟩⟨ cExp cT cA ⟩ cp))

record _=RightKanExt_along_ {cT cA cB} (ck : cA c→ cB) (cf : cT c→ cB) (cp : cT c→ cA) : Set ℓ? where
  field
    pf-right-kan-ext : (c-comp c∘ (c-id c, c-const⟨ cExp cA cB ⟩⟨ cExp cT cA ⟩ cp)) ⊣[ cf ↦ ck ]
{-
_=RightKanExt_along_ : ∀{cT cA cB} (ck : cA c→ cB) (cf : cT c→ cB) (cp : cT c→ cA) → Set ℓ?
ck =RightKanExt cf along cp = c-op ck =LeftKanExt c-op cf along c-op cp
-}
