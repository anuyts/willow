module willow.cat.Groupoids.LocalizationFunctor where

open import willow.cat.Groupoids public
open import willow.cat.Locpath.Fuse public

cloc : {ℓo ℓh : Level} → cCat ℓo ℓh ++> cGrpd ℓo (ℓo ⊔ ℓh)

f.obj cloc cA = mk-grpd (cLoc cA) (locIsGrpd cA)

f.obj (f.hom cloc cf) = f.obj cf
f.hom (f.hom cloc cf) lp = mapLocpath cf lp
f.hom-id' (f.hom cloc cf) x = refl
f.hom-m∘' (f.hom cloc cf) ψ φ = map-lp• cf φ ψ

f.hom-id' cloc cA = functorext (pair-ext refl
      (λi= x => λi= y => λ= lp => mapLocpath-id cA lp)
    )

f.hom-m∘' cloc {cA}{cB}{cC} cg cf = functorext (pair-ext refl
      (λi= x => λi= y => λ= lp => mapLocpath-c∘ cg cf lp)
    )
