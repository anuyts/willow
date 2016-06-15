module willow.cat.Cone where

open import willow.cat.Category public
open import willow.cat.Opposite public
open import willow.cat.Product public
open import willow.cat.Sets public

record Cone {ℓoA ℓhA ℓoI ℓhI} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
  (a : c.Obj cA) (cd : cI ++> cA) : Set (ℓhI ⊔ ℓoI ⊔ ℓhA) where
  no-eta-equality
  constructor mk-cone
  field
    obj : (i : c.Obj cI) → c.Hom cA a (f.obj cd i)
    hom : {i j : c.Obj cI} → (η : c.Hom cI i j) → (cA $ f.hom cd η m∘ obj i) == obj j

cone-ext : ∀{ℓoA ℓhA ℓoI ℓhI} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
  {a : c.Obj cA} {cd : cI ++> cA}
  {qa qb : Cone a cd} (p : Cone.obj qa == Cone.obj qb) → qa == qb
cone-ext {cA = cA}{cI}{a}{cd}{mk-cone obj ahom}{mk-cone .obj bhom} refl =
  map= (mk-cone obj) (λ¶i i => λ¶i j => λ¶ η => uip)

cCone : ∀{ℓoA ℓhA ℓoI ℓhI} → {cA : Cat ℓoA ℓhA} → (cI : Cat ℓoI ℓhI)
  → ((cOp cA) c× (cExp cI cA)) ++> cSet (ℓoI ⊔ ℓhI ⊔ ℓhA)
f.obj (cCone cI) a,cd = Cone (prl a,cd) (prr a,cd)
Cone.obj (f.hom (cCone {cA = cA} cI) φ,nta q) i = cA $ nt.obj (prr φ,nta) i m∘ (cA $ Cone.obj q i m∘ prl φ,nta)
Cone.hom (f.hom (cCone {cA = cA} cI) {a,cd}{a',cd'} φ,nta q) {i}{j} η =
  let a = prl a,cd
      cd = prr a,cd
      a' = prl a',cd'
      cd' = prr a',cd'
      φ = prl φ,nta
      nta = prr φ,nta
  in
    via cA $ f.hom cd' η m∘ (cA $ nt.obj nta i m∘ (cA $ Cone.obj q i m∘ φ)) $ refl •
    via cA $ (cA $ f.hom cd' η m∘ nt.obj nta i) m∘ (cA $ Cone.obj q i m∘ φ) $ sym (c.m∘assoc cA) •
    via cA $ (cA $ nt.obj nta j m∘ f.hom cd η) m∘ (cA $ Cone.obj q i m∘ φ)
      $ map= (λ ξ → cA $ ξ m∘ (cA $ Cone.obj q i m∘ prl φ,nta)) (nt.hom nta η) •
    via cA $ nt.obj nta j m∘ (cA $ f.hom cd η m∘ (cA $ Cone.obj q i m∘ φ)) $ c.m∘assoc cA •
    via cA $ nt.obj nta j m∘ (cA $ (cA $ f.hom cd η m∘ Cone.obj q i) m∘ φ)
      $ map= (λ ξ → cA $ nt.obj nta j m∘ ξ) (sym (c.m∘assoc cA)) •
    via cA $ nt.obj nta j m∘ (cA $ Cone.obj q j m∘ φ)
      $ map= (λ ξ → cA $ nt.obj nta j m∘ (cA $ ξ m∘ φ)) (Cone.hom q η) •
    refl
f.hom-id (cCone {cA = cA} cI) (a,cd) = λ= q => cone-ext (λ= i => (c.m∘lunit cA • c.m∘runit cA))
f.hom-m∘ (cCone {cA = cA} cI) {x,cd}{y,cd'}{z,cd''} ψ,ntb φ,nta = λ= q => cone-ext (λ= i =>
  let x = prl x,cd
      y = prl y,cd'
      z = prl z,cd''
      φ = prl φ,nta
      ψ = prl ψ,ntb
      cd = prr x,cd
      cd' = prr y,cd'
      cd'' = prr z,cd''
      nta = prr φ,nta
      ntb = prr ψ,ntb
  in
    refl •
    map= (λ ξ → cA $ (cA $ nt.obj ntb i m∘ nt.obj nta i) m∘ ξ) (sym (c.m∘assoc cA)) •
    c.m∘assoc cA •
    map= (λ ξ → cA $ nt.obj ntb i m∘ ξ) (sym (c.m∘assoc cA))
  )
