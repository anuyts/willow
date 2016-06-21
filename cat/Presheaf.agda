open import willow.cat.Category
open import willow.cat.Opposite
open import willow.cat.Sets
open import willow.cat.Limits
open import willow.cat.OfElements

module willow.cat.Presheaf {ℓoW ℓhW : Level} (ℓ : Level) (cW : Cat ℓoW ℓhW) where

Psh : Set ((lsuc ℓ) ⊔ ℓhW ⊔ ℓoW)
Psh = cOp cW ++> cSet ℓ

cPsh : Cat (ℓoW ⊔ ℓhW ⊔ lsuc ℓ) (ℓoW ⊔ ℓhW ⊔ lsuc ℓ)
cPsh = cExp (cOp cW) (cSet ℓ)

p⊤ : Psh
p⊤ = cConst (Lift ⊤)

p⊤intro : {pA : Psh} → pA nt→ p⊤
nt.obj p⊤intro w a = lift unit
nt.hom p⊤intro ρ = refl

isterminal-p⊤ : IsTerminal cPsh p⊤
--map void cones from pA to morphisms pA → p⊤
nt.obj (≅.fwd isterminal-p⊤) pA q = lift p⊤intro
nt.hom (≅.fwd isterminal-p⊤) {pA} {pB} pf = λ= q => map= lift (nt-ext refl)
--map morphisms pA → p⊤ to void cones from pA
nt.obj (≅.bck isterminal-p⊤) pA liftp* = mk-cone (λ()) (λ{})
nt.hom (≅.bck isterminal-p⊤) {pA} {pB} pf = λ= liftp* => cone-ext (funext (λ()))
≅.src-id isterminal-p⊤ = nt-ext (λ= pA => λ= q => cone-ext (funext (λ())))
≅.tgt-id isterminal-p⊤ = nt-ext (λ= pA => λ= liftp* => map= lift (nt-ext (λ= w => λ= a => map= lift is¶⊤)))

DPsh : (ℓtm : Level) → (pA : Psh) → Set ((lsuc ℓtm) ⊔ ℓ ⊔ ℓhW ⊔ ℓoW)
DPsh ℓtm pA = cOp∫ pA ++> cSet ℓtm
