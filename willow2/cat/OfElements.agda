{-# OPTIONS --type-in-type #-}

module willow2.cat.OfElements where

open import willow2.cat.Category
open import willow2.cat.OfSets
open import Data.Product public
open import willow2.basic.Subset public
open import willow2.cat.Opposite

c∫ : ∀{ℓf} (cA : Cat) → (cf : cA c→ cSet ℓf) → Cat
ℓo (c∫ {ℓf} cA cf) = ℓo cA ⊔ ℓf
ℓh (c∫ {ℓf} cA cf) = ℓh cA ⊔ ℓf
Obj (c∫ {ℓf} cA cf) = Σ[ a ∈ Obj cA ] obj cf a
Hom (c∫ {ℓf} cA cf) (a1 , t1) (a2 , t2) = [ φ ∈ Hom cA a1 a2 ! hom cf φ t1 ≡ t2 ]
IsCat.id⟨_⟩ (isCat (c∫ {ℓf} cA cf)) (a , t) = id , cong-app (hom-id cf) t
IsCat._∘_ (isCat (c∫ {ℓf} cA cf)) {a1 , t1} {a2 , t2} {a3 , t3} (ψ , eψ) (φ , eφ) = (ψ ∘ φ) , (begin
  hom cf (ψ ∘ φ) t1
    ≡⟨ cong-app (hom-comp cf ψ φ) t1 ⟩
  hom cf ψ (hom cf φ t1)
    ≡⟨ cong (hom cf ψ) eφ ⟩
  hom cf ψ t2
    ≡⟨ eψ ⟩
  t3 ∎)
IsCat.assoc (isCat (c∫ {ℓf} cA cf)) (ψ , eψ) (χ , eχ) (φ , eφ) = ext-Subset (assoc ψ χ φ)
IsCat.lunit (isCat (c∫ {ℓf} cA cf)) (φ , e) = ext-Subset (lunit φ)
IsCat.runit (isCat (c∫ {ℓf} cA cf)) (φ , e) = ext-Subset (runit φ)

c-proj : ∀{ℓf cA} (cf : cA c→ cSet ℓf) → (c∫ cA cf c→ cA)
obj (c-proj {ℓf} {cA} cf) (a , t) = a
hom (c-proj {ℓf} {cA} cf) (φ , e) = φ
hom-id (c-proj {ℓf} {cA} cf) = refl
hom-comp (c-proj {ℓf} {cA} cf) ψ φ = refl

c∫⁻ : ∀{ℓf} (cA : Cat) → (cf : cOp cA c→ cSet ℓf) → Cat
c∫⁻ cA cf = cOp (c∫ (cOp cA) cf)

c-proj⁻ : ∀{ℓf cA} (cf : cOp cA c→ cSet ℓf) → (c∫⁻ cA cf c→ cA)
c-proj⁻ {ℓf}{cA} cf = c-op (c-proj cf)
