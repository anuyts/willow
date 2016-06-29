module willow.cat.Sets.Limits where

open import willow.cat.Sets public
open import willow.cat.Limits public
open import willow.basic.Propositional.HeteroIdentity public

record Lim {ℓoI ℓhI ℓ} {cI : Cat ℓoI ℓhI} (cd : cI ++> cSet ℓ) : Set (ℓ ⊔ ℓoI ⊔ ℓhI) where
  no-eta-equality
  constructor mk-lim
  field
    obj : (i : c.Obj cI) → f.obj cd i
    hom : {i j : c.Obj cI} → (η : c.Hom cI i j) → f.hom cd η (obj i) == obj j

lim-ext : ∀{ℓoI ℓhI ℓ} {cI : Cat ℓoI ℓhI} {cd : cI ++> cSet ℓ} {la lb : Lim cd} (p : Lim.obj la == Lim.obj lb) → la == lb
lim-ext {cI = cI}{cd}{mk-lim obj ahom}{mk-lim .obj bhom} refl = map= (mk-lim obj) (λ¶i i => λ¶i j => λ¶ η => uip)

h-lim-ext : ∀{ℓoI ℓhI ℓ} {cI : Cat ℓoI ℓhI} {cd cd' : cI ++> cSet ℓ} (p : cd == cd') {la : Lim cd} {lb : Lim cd'}
  (p : Lim.obj la === Lim.obj lb) → la === lb
h-lim-ext {cI = cI}{cd}{.cd} refl {mk-lim obj ahom}{mk-lim .obj bhom} hrefl =
  hdmap= (mk-lim obj) (λ¶i i => λ¶i j => λ¶ η => uip)

-----------------------------------------------------------------------------------------

cSetHasLimits : ∀{ℓ} → HasLimits (cSet ℓ) ℓ ℓ

prl (cSetHasLimits {ℓ} {cI} cd) = Lim cd

--≅.fwd is a NT that maps cones from X to maps (X → Lim cd)
--(lower ... x) is the element of the limit you get for x : X
Lim.obj (lower (nt.obj (≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) X q) x) i = Cone.obj q i x
Lim.hom (lower (nt.obj (≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) X q) x) {i}{j} η =
  map= (λ h → h x) (Cone.hom q η)
nt.hom (≅.fwd (prr (cSetHasLimits {ℓ} {cI} cd))) {Y}{X} f = λ= q => map= lift (λ= x => lim-ext refl)

--≅.bck is a NT that maps maps (X → Lim cd) to cones from X
Cone.obj (nt.obj (≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) X (lift g)) i x = Lim.obj (g x) i
Cone.hom (nt.obj (≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) X (lift g)) {i}{j} η = λ= x => Lim.hom (g x) η
nt.hom (≅.bck (prr (cSetHasLimits {ℓ} {cI} cd))) {Y}{X} f = λ= liftg => cone-ext refl

≅.src-id (prr (cSetHasLimits {ℓ} {cI} cd)) = nt-ext (λ= X => λ= q => cone-ext (λ= i => λ= x => refl))

≅.tgt-id (prr (cSetHasLimits {ℓ} {cI} cd)) = nt-ext (λ= X => λ= liftg => map= lift (λ= x => lim-ext refl))

-----------------------------------------------------------------------------------------

mapLim : ∀{ℓoI ℓhI ℓ} {cI : Cat ℓoI ℓhI} {cf cg : cI ++> cSet ℓ} (nta : cf nt→ cg) → (Lim cf → Lim cg)
Lim.obj (mapLim nta l) i = nt.obj nta i (Lim.obj l i)
Lim.hom (mapLim {cI = cI} {cf} {cg} nta l) {i}{j} η =
  via (f.hom cg η ∘ nt.obj nta i) (Lim.obj l i) $ refl •
  via (nt.obj nta j ∘ f.hom cf η) (Lim.obj l i) $ happly (nt.hom nta η) (Lim.obj l i) •
  via (nt.obj nta j) (Lim.obj l j) $ map= (nt.obj nta j) (Lim.hom l η) •
  refl

restrLim : ∀{ℓoI ℓhI ℓoJ ℓhJ ℓ} {cI : Cat ℓoI ℓhI} {cJ : Cat ℓoJ ℓhJ} {cd : cJ ++> cSet ℓ}
  (ci : cI ++> cJ) → (Lim cd → Lim (cd c∘ ci))
Lim.obj (restrLim ci l) i = Lim.obj l (f.obj ci i)
Lim.hom (restrLim ci l) {i}{i'} η = Lim.hom l (f.hom ci η)

-----------------------------------------------------------------------------------------

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
