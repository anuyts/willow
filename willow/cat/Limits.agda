module willow.cat.Limits where

open import willow.cat.Category public
open import willow.cat.Isomorphism public
open import willow.cat.Cone public
open import willow.cat.HomFunctor public
open import willow.cat.Lift public
open import willow.cat.Exponential public

IsLimit : ∀{ℓoA ℓhA ℓoI ℓhI} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
  (a : c.Obj cA) (cd : cI ++> cA) → Set (lsuc ℓhI ⊔ (lsuc ℓoI ⊔ (lsuc ℓhA ⊔ ℓoA)))
IsLimit {ℓoA}{ℓhA}{ℓoI}{ℓhI} {cA} {cI} a cd =
  Iso (cExp (cOp cA) (cSet _))
    (cCone {cA = cA} cI c∘ (c-id (cOp cA) c⊠ cConst {cB = cExp cI cA} cd))
    (c-setlift ℓhA (ℓoI ⊔ ℓhI ⊔ ℓhA) c∘ cHom (cA) c∘ (c-id (cOp cA) c⊠ cConst {cB = cA} a))

record [IsLimit] {ℓoA ℓhA ℓoI ℓhI : Level} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
       (a : c.Obj cA) (cd : cI ++> cA) : Set (lsuc ℓhI ⊔ (lsuc ℓoI ⊔ (lsuc ℓhA ⊔ ℓoA))) where
  constructor wrap
  no-eta-equality
  field
    use : IsLimit a cd

IsTerminal : ∀{ℓoA ℓhA} (cA : Cat ℓoA ℓhA) (a : c.Obj cA) → Set (lsuc ℓhA ⊔ ℓoA)
IsTerminal cA a = IsLimit {cA = cA} a c⊥elim

[IsTerminal] : ∀{ℓoA ℓhA} (cA : Cat ℓoA ℓhA) (a : c.Obj cA) → Set (lsuc ℓhA ⊔ ℓoA)
[IsTerminal] cA a = [IsLimit] {cA = cA} a c⊥elim

cone-out : ∀{ℓoA ℓhA ℓoI ℓhI} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
  {a : c.Obj cA} {cd : cI ++> cA} (p : IsLimit a cd) → Cone a cd
cone-out {cA = cA}{a = a}{cd} p = nt.obj (≅.bck p) a (lift (c.id cA a))

hom-to-cone : ∀{ℓoA ℓhA ℓoI ℓhI} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
  {a : c.Obj cA} {cd : cI ++> cA} (p : IsLimit a cd) {x : c.Obj cA} (φ : c.Hom cA x a) → Cone x cd
hom-to-cone {cA = cA}{a = a}{cd} p {x} φ = nt.obj (≅.bck p) x (lift φ)

cone-to-hom : ∀{ℓoA ℓhA ℓoI ℓhI} {cA : Cat ℓoA ℓhA} {cI : Cat ℓoI ℓhI}
  {a : c.Obj cA} {cd : cI ++> cA} (p : IsLimit a cd) {x : c.Obj cA} (q : Cone x cd) → c.Hom cA x a
cone-to-hom {cA = cA}{a = a}{cd} p {x} q = lower (nt.obj (≅.fwd p) x q)

HasLimits : ∀{ℓoA ℓhA} (cA : Cat ℓoA ℓhA) (ℓoI ℓhI : Level) → Set (lsuc ℓhI ⊔ (lsuc ℓoI ⊔ (lsuc ℓhA ⊔ ℓoA)))
HasLimits cA ℓoI ℓhI = {cI : Cat ℓoI ℓhI} (cd : cI ++> cA) → Sum λ(a : c.Obj cA) → IsLimit a cd
