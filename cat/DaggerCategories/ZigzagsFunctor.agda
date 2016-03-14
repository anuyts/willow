module willow.cat.DaggerCategories.ZigzagsFunctor where

open import willow.cat.DaggerCategories public
open import willow.cat.Zigzag.DaggerFuse public

czigzags : {ℓo ℓh : Level} → cCat ℓo ℓh ++> cDCat ℓo (ℓo ⊔ ℓh)

_++>_.obj czigzags c = dcZigzags c

_++>_.obj (_dc→_.f (_++>_.hom czigzags cf)) = f.obj cf
_++>_.hom (_dc→_.f (_++>_.hom czigzags cf)) ζ = mapZigzag cf ζ
_++>_.hom-id (_dc→_.f (_++>_.hom czigzags cf)) x = refl
_++>_.hom-m∘ (_dc→_.f (_++>_.hom czigzags cf)) η ζ = map-zz• cf ζ η
_dc→_.hom-† (_++>_.hom czigzags cf) ζ = {!!} -- prove that inverse commutes with map.

_++>_.hom-id czigzags c = dfunctorext (functorext (pair-ext refl
    (λi= x => λi= y => λ= ζ => mapZigzag-id c ζ)
  ))

_++>_.hom-m∘ czigzags cg cf = dfunctorext (functorext (pair-ext refl
    (λi= x => λi= y => λ= ζ => mapZigzag-c∘ cg cf ζ)
  ))
