module aken.cat.Groupoids.LocalizationFunctor where

open import aken.cat.Groupoids public
open import aken.cat.Adjunction public
open import aken.cat.Locpath.Fuse public

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
      (λi= x => λi= y => λ= lp => mapLocpath-m∘ cg cf lp)
    )
  }

cloc⊣cforgetGrpd : ∀{ℓo ℓh} → cloc{ℓo}{ℓo ⊔ ℓh} ⊣ cforgetGrpd{ℓo}{ℓo ⊔ ℓh}
cloc⊣cforgetGrpd = record
  { iso = λ {cL gR} → record
    { fwd = λ cf → record
      { obj = λ x → f.obj cf x
      ; hom = λ lp → fuseLocpath gR {!!}
      ; hom-id = {!!}
      ; hom-m∘ = {!!}
      }
    ; bck = λ cg → record
      { obj = λ x → f.obj cg x
      ; hom = {!!}
      ; hom-id = {!!}
      ; hom-m∘ = {!!}
      }
    ; src-id = {!!}
    ; tgt-id = {!!}
    }
  ; fwd-m∘ = {!!}
  ; bck-m∘ = {!!}
  }
