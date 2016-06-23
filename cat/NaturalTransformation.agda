module willow.cat.NaturalTransformation where

open import willow.cat.Category
open import willow.basic.Identity

nt-transport : ∀{ℓoA ℓhA ℓoB ℓhB ℓE} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {E : Set ℓE} {e e' : E}
  (f : E → cA ++> cB) → (e == e') → (f e nt→ f e')
nt.obj (nt-transport {cB = cB} cf (refl {e})) x = c.id cB (f.obj (cf e) x)
nt.hom (nt-transport {cB = cB} cf (refl {e})) φ = c.m∘runit cB • sym (c.m∘lunit cB)

nt-tra_/_ : ∀{ℓoA ℓhA ℓoB ℓhB ℓE} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {E : Set ℓE} {e e' : E}
  (f : E → cA ++> cB) → (e == e') → (f e nt→ f e')
nt-tra_/_ = nt-transport

nt-tra-loop : ∀{ℓoA ℓhA ℓoB ℓhB ℓE} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {E : Set ℓE} {e : E}
  (f : E → cA ++> cB) → (p : e == e) → (nt-tra f / p) == nt-id (f e)
nt-tra-loop {e = e} f p =
  via (nt-tra f / (refl {a = e})) $ map= (λ q → nt-tra f / q) (p == refl ∋ uip) •
  nt-ext refl
