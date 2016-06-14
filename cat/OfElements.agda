module willow.cat.OfElements where

open import willow.cat.Category public
open import willow.cat.Sets public
open import willow.basic.UIP public
open import willow.cat.Opposite public

c∫ : ∀{ℓoA ℓhA ℓf} → {cA : Cat ℓoA ℓhA} → (cf : cA ++> cSet ℓf) → Cat (ℓf ⊔ ℓoA) (ℓf ⊔ ℓhA)
Cat.Obj (c∫ {cA = cA} cf) = Sum (λ (x : c.Obj cA) → f.obj cf x)
Cat.Hom (c∫ {cA = cA} cf) x y = Sum (λ (φ : c.Hom cA (prl x) (prl y)) → (f.hom cf φ) (prr x) == prr y)
prl (Cat.id (c∫ {cA = cA} cf) x) = (c.id cA (prl x))
prr (Cat.id (c∫ {cA = cA} cf) x) = map= (λ f → f(prr x)) (f.hom-id cf (prl x))
prl (Cat.comp (c∫ {cA = cA} cf) ψ φ) = c.comp cA (prl ψ) (prl φ)
prr (Cat.comp (c∫ {cA = cA} cf) {x}{y}{z} ψ φ) =
  map= (λ f → f(prr x)) (f.hom-m∘ cf (prl ψ) (prl φ)) •
  map= (f.hom cf (prl ψ)) (prr φ) •
  prr ψ
Cat.m∘assoc (c∫ {cA = cA} cf) = pair-ext (c.m∘assoc cA) uip
Cat.m∘lunit (c∫ {cA = cA} cf) = pair-ext (c.m∘lunit cA) uip
Cat.m∘runit (c∫ {cA = cA} cf) = pair-ext (c.m∘runit cA) uip

c-pr : ∀{ℓoA ℓhA ℓf} → {cA : Cat ℓoA ℓhA} → {cf : cA ++> cSet ℓf} → c∫ cf ++> cA
f.obj c-pr x = prl x
f.hom c-pr φ = prl φ
f.hom-id c-pr x = refl
f.hom-m∘ c-pr ψ φ = refl

cOp∫ : ∀{ℓoA ℓhA ℓf} → {cA : Cat ℓoA ℓhA} → (cf : cA ++> cSet ℓf) → Cat (ℓf ⊔ ℓoA) (ℓf ⊔ ℓhA)
cOp∫ cf = cOp (c∫ cf)

c-co-pr : ∀{ℓoA ℓhA ℓf} → {cA : Cat ℓoA ℓhA} → {cf : cOp cA ++> cSet ℓf} → cOp∫ cf ++> cA
f.obj c-co-pr x = prl x
f.hom c-co-pr φ = prl φ
f.hom-id c-co-pr x = refl
f.hom-m∘ c-co-pr ψ φ = refl
