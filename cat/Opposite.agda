module willow.cat.Opposite where

open import willow.cat.Category
open import willow.cat.Categories
open import willow.cat.Isomorphism public

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

≅OpOp : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Iso (cCat ℓo ℓh) c (cOp (cOp c))
--
f.obj (Iso.fwd (≅OpOp c)) x = x
f.hom (Iso.fwd (≅OpOp c)) φ = φ
f.hom-id (Iso.fwd (≅OpOp c)) x = refl
f.hom-m∘ (Iso.fwd (≅OpOp c)) ψ φ = refl
--
f.obj (Iso.bck (≅OpOp c)) x = x
f.hom (Iso.bck (≅OpOp c)) φ = φ
f.hom-id (Iso.bck (≅OpOp c)) x = refl
f.hom-m∘ (Iso.bck (≅OpOp c)) ψ φ = refl
--
≅.src-id (≅OpOp c) = refl
--
≅.tgt-id (≅OpOp c) = refl

nt-op : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB}
  → {cf cg : cA ++> cB} → (nta : cf nt→ cg) → (c-op cg nt→ c-op cf)
nt.obj (nt-op nta) x = nt.obj nta x
nt.hom (nt-op nta) φ = sym (nt.hom nta φ)
