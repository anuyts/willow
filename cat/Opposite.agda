module willow.cat.Opposite where

open import willow.cat.Category

cOp : ∀{ℓo ℓh} → Cat ℓo ℓh → Cat ℓo ℓh
cOp c = record
  { Obj = c.Obj c
  ; Hom = λ x y → c.Hom c y x
  ; id = c.id c
  ; comp = λ ψ φ → c $ φ m∘ ψ
  ; m∘assoc = λ {w} {x} {y} {z} {ψ} {ξ} {φ} → sym (c.m∘assoc c)
  ; m∘lunit = λ {x} {y} {φ} → c.m∘runit c
  ; m∘runit = λ {x} {y} {φ} → c.m∘lunit c
  }

c-op : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB) → (cOp cA ++> cOp cB)
c-op cf = record
  { obj = f.obj cf
  ; hom = f.hom cf
  ; hom-id = f.hom-id cf
  ; hom-m∘ = λ ψ φ → f.hom-m∘ cf φ ψ
  }
