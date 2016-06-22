module willow.cat.Opposite where

open import willow.cat.Category
open import willow.cat.Categories
open import willow.cat.Isomorphism public

cOp : ∀{ℓo ℓh} → Cat ℓo ℓh → Cat ℓo ℓh
c.Obj (cOp c) = c.Obj c
c.Hom (cOp c) x y = c.Hom c y x
c.id (cOp c) x = c.id c x
c.comp (cOp c) ψ φ = c $ φ m∘ ψ
c.m∘assoc (cOp c) = sym (c.m∘assoc c)
c.m∘lunit (cOp c) = c.m∘runit c
c.m∘runit (cOp c) = c.m∘lunit c

c-op : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB) → (cOp cA ++> cOp cB)
f.obj (c-op cf) = f.obj cf
f.hom (c-op cf) = f.hom cf
f.hom-id (c-op cf) = f.hom-id cf
f.hom-m∘ (c-op cf) ψ φ = f.hom-m∘ cf φ ψ

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
≅.src-id (≅OpOp c) = functorext refl
--
≅.tgt-id (≅OpOp c) = functorext refl

nt-op : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB}
  → {cf cg : cA ++> cB} → (nta : cf nt→ cg) → (c-op cg nt→ c-op cf)
nt.obj (nt-op nta) x = nt.obj nta x
nt.hom (nt-op nta) φ = sym (nt.hom nta φ)
