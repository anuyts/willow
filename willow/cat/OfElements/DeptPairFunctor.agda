module willow.cat.OfElements.DeptPairFunctor where

open import willow.cat.OfElements public

cDeptPair : ∀{ℓoA ℓhA ℓoB ℓhB ℓ} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB}
  → {cf : cA ++> cSet ℓ} → {cg : cB ++> cSet ℓ}
  → (ck : c∫ cf ++> cB) → (nta : cf c∘ c-pr nt→ cg c∘ ck) → (c∫ cf ++> c∫ cg)
f.obj (cDeptPair {cA = cA}{cB} {cf}{cg} ck nta) a,s = f.obj ck (a,s) , nt.obj nta (a,s) (prr a,s)
prl (f.hom (cDeptPair {cA = cA}{cB} {cf}{cg} ck nta) {a,s}{a',s'} α,p) = f.hom ck (α,p)
prr (f.hom (cDeptPair {cA = cA}{cB} {cf}{cg} ck nta) {a,s}{a',s'} α,p) =
  via ((f.hom (cg c∘ ck) α,p) ∘ (nt.obj nta a,s)) (prr a,s) $ refl •
  via (nt.obj nta (a',s') ∘ f.hom (cf c∘ (c-pr {cf = cf})) α,p) (prr a,s) $ map= (λ h → h (prr a,s)) (nt.hom' nta α,p) •
  via nt.obj nta a',s' (prr a',s') $ map= (nt.obj nta a',s') (prr α,p) • refl
f.hom-id' (cDeptPair {cA = cA}{cB} {cf}{cg} ck nta) a,s = pair-ext (f.hom-id' ck a,s) uip
f.hom-m∘' (cDeptPair {cA = cA}{cB} {cf}{cg} ck nta) α,p α',p' = pair-ext (f.hom-m∘' ck α,p α',p') uip

cOpDeptPair : ∀{ℓoA ℓhA ℓoB ℓhB ℓ} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB}
  → {cf : cOp cA ++> cSet ℓ} → {cg : cOp cB ++> cSet ℓ}
  → (ck : cOp∫ cf ++> cB) → (nta : cf c∘ c-op {cB = cA} (c-co-pr {cf = cf}) nt→ cg c∘ c-op ck) → (cOp∫ cf ++> cOp∫ cg)
f.obj (cOpDeptPair {cA = cA}{cB} {cf}{cg} ck nta) a,s = f.obj ck (a,s) , nt.obj nta (a,s) (prr a,s)
f.hom (cOpDeptPair {cA = cA}{cB} {cf}{cg} ck nta) {a',s'}{a,s} α,p = f.hom ck (α,p) ,
  via ((f.hom (cg c∘ c-op ck) α,p) ∘ (nt.obj nta a,s)) (prr a,s) $ refl •
  via (nt.obj nta (a',s') ∘ f.hom (cf c∘ (c-pr {cf = cf})) α,p) (prr a,s) $ map= (λ h → h (prr a,s)) (nt.hom' nta α,p) •
  via nt.obj nta a',s' (prr a',s') $ map= (nt.obj nta a',s') (prr α,p) • refl
f.hom-id' (cOpDeptPair {cA = cA}{cB} {cf}{cg} ck nta) a,s = pair-ext (f.hom-id' ck a,s) uip
f.hom-m∘' (cOpDeptPair {cA = cA}{cB} {cf}{cg} ck nta) α,p α',p' = pair-ext (f.hom-m∘' ck α,p α',p') uip
