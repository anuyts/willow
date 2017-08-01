{-# OPTIONS --type-in-type #-}

module willow2.cat.Limit.Local where

open import willow2.cat.Category
open import willow2.cat.KanExtension.Local public
open import willow2.cat.Unit public

record _=Colim_ {cI cA} (colim : Obj cA) (cd : cI c→ cA) : Set ℓ? where
  field
    pf-colim : c-const colim =LeftKanExt cd along c-tt

record _=Lim_ {cI cA} (lim : Obj cA) (cd : cI c→ cA) : Set ℓ? where
  field
    pf-lim : c-const lim =RightKanExt cd along c-tt

{-
_=Lim_ : ∀ {cI cA} (lim : Obj cA) (cd : cI c→ cA) → Set ℓ?
lim =Lim cd = lim =Colim c-op cd
-}

module Terminal where
  open import willow2.cat.Empty public
  
  IsTerminal : (cA : Cat) → (t : Obj cA) → Set ℓ?
  IsTerminal cA t = t =Lim c-absurd {cA}
