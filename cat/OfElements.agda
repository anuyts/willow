module willow.cat.OfElements where

open import willow.cat.Category public
open import willow.cat.Sets public
open import willow.basic.UIP public
open import willow.cat.Opposite public

c∫ : ∀{ℓoA ℓhA ℓf} → {cA : Cat ℓoA ℓhA} → (cf : cA ++> cSet ℓf) → Cat (ℓf ⊔ ℓoA) (ℓf ⊔ ℓhA)
Cat.Obj (c∫ {cA = cA} cf) = Sum (λ (x : c.Obj cA) → f.obj cf x)
Cat.Hom (c∫ {cA = cA} cf) x y = Sum (λ (φ : c.Hom cA (prl x) (prl y)) → (f.hom cf φ) (prr x) == prr y)
Cat.id (c∫ {cA = cA} cf) x = (c.id cA (prl x)) , map= (λ f → f(prr x)) (f.hom-id cf (prl x))
Cat.comp (c∫ {cA = cA} cf) {x}{y}{z} ψ φ = c.comp cA (prl ψ) (prl φ) , (
    map= (λ f → f(prr x)) (f.hom-m∘ cf (prl ψ) (prl φ)) •
    map= (f.hom cf (prl ψ)) (prr φ) •
    prr ψ
  )
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

c∫-hom : ∀{ℓoA ℓhA ℓf} {cA : Cat ℓoA ℓhA} → {cf cg : cA ++> cSet ℓf} → (nta : cf nt→ cg) → c∫ cf ++> c∫ cg
f.obj (c∫-hom nta) a,x = (prl a,x) , (nt.obj nta (prl a,x) (prr a,x))
f.hom (c∫-hom {cA = cA}{cf}{cg} nta) {a,x} {b,y} φ,p = prl φ,p ,
  via (f.hom cg (prl φ,p) ∘ nt.obj nta (prl a,x)) (prr a,x) $ refl •
  via (nt.obj nta (prl b,y) ∘ f.hom cf (prl φ,p)) (prr a,x) $ happly (nt.hom nta (prl φ,p)) (prr a,x) •
  via (nt.obj nta (prl b,y)) (prr b,y) $ map= (nt.obj nta (prl b,y)) (prr φ,p) •
  refl
f.hom-id (c∫-hom nta) a,x = pair-ext refl uip
f.hom-m∘ (c∫-hom nta) ψ,q φ,p = pair-ext refl uip

cOp∫-hom : ∀{ℓoA ℓhA ℓf} {cA : Cat ℓoA ℓhA} → {cf cg : cA ++> cSet ℓf} → (nta : cf nt→ cg) → cOp∫ cf ++> cOp∫ cg
cOp∫-hom nta = c-op (c∫-hom nta)
