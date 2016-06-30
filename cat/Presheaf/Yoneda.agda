open import willow.cat.Category public
open import willow.cat.HomFunctor public
open import willow.cat.Currying public
import willow.cat.Presheaf

module willow.cat.Presheaf.Yoneda {ℓoW ℓhW : Level} (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓhW cW

cYoneda : cW ++> cPsh
cYoneda = c-curried cW (cOp cW) (cSet ℓhW) (cHom cW c∘ c-swap)

pY : c.Obj cW → Psh
pY = f.obj cYoneda
