module willow.cat.Groupoids.LocalizationFunctor where

open import willow.cat.Groupoids public
open import willow.cat.Locpath.Fuse public

cloc : {ℓo ℓh : Level} → cCat ℓo ℓh ++> cGrpd ℓo (ℓo ⊔ ℓh)
cloc = record
  { obj = λ cA → mk-grpd (cLoc cA) (locIsGrpd cA)
  ; hom = λ {cA cB} cf → record
    { obj = f.obj cf
    ; hom = λ {x y} lp → mapLocpath cf lp
    ; hom-id = λ x → refl
    ; hom-m∘ = λ {x y z} ψ φ → map-lp• cf φ ψ
    }
  ; hom-id = λ cA → functorext (pair-ext refl
      (λi= x => λi= y => λ= lp => mapLocpath-id cA lp)
    )
  ; hom-m∘ = λ {cA cB cC} cg cf → functorext (pair-ext refl
      (λi= x => λi= y => λ= lp => mapLocpath-c∘ cg cf lp)
    )
  }
