module willow.cat.Sets.Limits where

open import willow.cat.Sets public
open import willow.cat.Limits public

record Lim {ℓoI ℓhI ℓ} {cI : Cat ℓoI ℓhI} (cd : cI ++> cSet ℓ) : Set (ℓ ⊔ ℓoI ⊔ ℓhI) where
  field
    obj : (i : c.Obj cI) → f.obj cd i
    hom : {i j : c.Obj cI} → (η : c.Hom cI i j) → f.hom cd η (obj i) == obj j



cSetHasLimits : ∀{ℓ} → HasLimits (cSet ℓ) ℓ ℓ

prl (cSetHasLimits {ℓ} {cI} cd) = Lim cd

--≅.fwd is a NT that maps cones from X to maps (X → Lim cd)
--(lower ... x) is the element of the limit you get for x : X
Lim.obj (lower (nt.obj (≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) X q) x) i = Cone.obj q i x
Lim.hom (lower (nt.obj (≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) X q) x) {i}{j} η =
  map= (λ h → h x) (Cone.hom q η)
nt.hom (≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) {Y}{X} f = λ= q => map= lift (λ= x => {!!}) -- need lim-ext

nt.obj (≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) = {!!}
nt.hom (≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) = {!!}

≅.src-id (prr (cSetHasLimits {ℓ} {cI} cd)) = {!!}

≅.tgt-id (prr (cSetHasLimits {ℓ} {cI} cd)) = {!!}

{-
cSetHasLimits : ∀{ℓ} → HasLimits (cSet ℓ) ℓ ℓ
prl (cSetHasLimits {ℓ} {cI} cd) = Cone (Lift ⊤) cd

{-
  ≅.fwd is a NT that maps cones from X to maps X → Cone ⊤ cd
  (lower ... x) is the Cone ⊤ you get for x : X
-}
Cone.obj (lower(nt.obj(≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) X q) x) i = (Cone.obj q i) ∘ (λ _ → x)
Cone.hom (lower(nt.obj(≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) X q) x) {i}{j} η =
  map= (λ h → h ∘ (λ _ → x)) (Cone.hom q η)
--show that it doesn't matter whether you first extend the cone and then make a morphism, or vice versa
nt.hom(≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) {Y}{X} f =
  λ= q => map= lift (λ= x => cone-ext
    --now we just show that the (Cone ⊤ cd)s are equal.
    refl
  )

{-
  ≅.bck is a NT that maps maps (X → Cone ⊤ cd) to cones from X.
-}
Cone.obj (nt.obj(≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) X (lift f)) i x = Cone.obj (f x) i (lift unit)
Cone.hom (nt.obj(≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) X (lift f)) {i}{j} η =
  λ= x => map= (λ h → (h (lift unit))) (Cone.hom (f x) η)
nt.hom(≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) {Y}{X} g = λ= liftf => cone-ext refl

≅.src-id (prr (cSetHasLimits {ℓ} {cI} cd)) = nt-ext (λ= X => λ= q => cone-ext (λ= i => λ= x => refl))
≅.tgt-id (prr (cSetHasLimits {ℓ} {cI} cd)) =
  nt-ext (λ= X => λ= liftf => map= lift (λ= x => cone-ext (λ= i => λ= _ =>
    map= (λ u → Cone.obj (lower liftf x) i (lift u)) is¶⊤
  )))




Limset : ∀{ℓ} {cI : Cat ℓ ℓ} (cd : cI ++> cSet ℓ) → Set ℓ
Limset cd = prl (cSetHasLimits cd)
-}
