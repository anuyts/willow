module willow.cat.DaggerCategories.ZigzagsFunctor where

open import willow.cat.DaggerCategories public
open import willow.cat.Zigzag.DaggerFuse public

czigzags : {ℓo ℓh : Level} → cCat ℓo ℓh ++> cDCat ℓo (ℓo ⊔ ℓh)

f.obj czigzags c = dcZigzags c

f.obj (df.f (f.hom czigzags cf)) = f.obj cf
f.hom (df.f (f.hom czigzags cf)) ζ = mapZigzag cf ζ
f.hom-id' (df.f (f.hom czigzags cf)) x = refl
f.hom-m∘' (df.f (f.hom czigzags cf)) η ζ = map-zz• cf ζ η
df.hom-† (f.hom czigzags cf) ζ = map-zz-inv cf ζ

f.hom-id' czigzags c = dfunctorext (functorext (pair-ext refl
    (λi= x => λi= y => λ= ζ => mapZigzag-id c ζ)
  ))

f.hom-m∘' czigzags cg cf = dfunctorext (functorext (pair-ext refl
    (λi= x => λi= y => λ= ζ => mapZigzag-c∘ cg cf ζ)
  ))
