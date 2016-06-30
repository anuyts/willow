module willow.cat.NaturalTransformation where

open import willow.cat.Category
open import willow.basic.Identity
open import willow.cat.Isomorphism public
open import willow.cat.Sets

nt-tra : ∀{ℓoA ℓhA ℓoB ℓhB} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {cf cg : cA ++> cB}
  → (cf == cg) → (cf nt→ cg)
nt-tra {cA = cA} {cB} {cf}{cg} p = ≅.fwd (i-tra (cExp cA cB) p)

nt-tra-set-lemma : ∀{ℓoA ℓhA ℓ} {cA : Cat ℓoA ℓhA} {cf cg : cA ++> cSet ℓ} (p : cf == cg) (x : c.Obj cA)
  → (nt.obj (nt-tra p) x == tra! (map= (λ ch → f.obj ch x) p))
nt-tra-set-lemma refl x = refl

{-
nt-transport : ∀{ℓoA ℓhA ℓoB ℓhB ℓE} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {E : Set ℓE} {e e' : E}
  (f : E → cA ++> cB) → (e == e') → (f e nt→ f e')
nt.obj (nt-transport {cB = cB} cf (refl {e})) x = c.id cB (f.obj (cf e) x)
nt.hom' (nt-transport {cB = cB} cf (refl {e})) φ = c.m∘runit' cB • sym (c.m∘lunit' cB)

nt-tra_/_ : ∀{ℓoA ℓhA ℓoB ℓhB ℓE} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {E : Set ℓE} {e e' : E}
  (f : E → cA ++> cB) → (e == e') → (f e nt→ f e')
nt-tra_/_ = nt-transport

nt-tra-loop : ∀{ℓoA ℓhA ℓoB ℓhB ℓE} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} {E : Set ℓE} {e : E}
  (f : E → cA ++> cB) → (p : e == e) → (nt-tra f / p) == nt-id (f e)
nt-tra-loop {e = e} f p =
  via (nt-tra f / (refl {a = e})) $ map= (λ q → nt-tra f / q) (p == refl ∋ uip) •
  nt-ext refl
-}
