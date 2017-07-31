{-# OPTIONS --type-in-type #-}

module willow2.cat.OfSets where

open import willow2.cat.Category

cSet : Level → Cat
ℓo (cSet ℓ) = suc ℓ
ℓh (cSet ℓ) = ℓ
Obj (cSet ℓ) = Set ℓ
Hom (cSet ℓ) X Y = X → Y
IsCat.id-at (isCat (cSet ℓ)) X = f-id
IsCat._∘_ (isCat (cSet ℓ)) g f = g f∘ f
IsCat.assoc (isCat (cSet ℓ)) h g f = refl
IsCat.lunit (isCat (cSet ℓ)) f = refl
IsCat.runit (isCat (cSet ℓ)) f = refl
