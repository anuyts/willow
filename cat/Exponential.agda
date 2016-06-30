module willow.cat.Exponential where

open import willow.cat.Category public

c-cConst : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → cB ++> cExp cA cB
f.obj c-cConst x = cConst x
nt.obj (f.hom c-cConst φ) x = φ
nt.hom (f.hom (c-cConst {cB = cB}) φ) ψ = c.m∘lunit cB • sym (c.m∘runit cB)
f.hom-id c-cConst x = nt-ext refl
f.hom-m∘ c-cConst ψ φ = nt-ext refl

c-eval : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (a : c.Obj cA) → cExp cA cB ++> cB
f.obj (c-eval a) cf = f.obj cf a
f.hom (c-eval a) {cg}{cf} nta = nt.obj nta a
f.hom-id (c-eval a) cf = refl
f.hom-m∘ (c-eval a) ntb nta = refl
