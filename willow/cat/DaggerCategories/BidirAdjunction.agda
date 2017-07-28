module willow.cat.DaggerCategories.BidirAdjunction where

open import willow.cat.DaggerCategories.BidirFunctor public
open import willow.cat.Adjunction public
open import willow.cat.DaggerCategory public

bidirAdjunction : ∀{ℓo ℓh} → cforgetDagger{ℓo}{ℓh} ⊣ cbidir{ℓo}{ℓh}

-- cf : L → R. Now create †-functor cf> : L → bidir R
f.obj (df.f (nt.obj (≅.fwd bidirAdjunction) dcL,cR cf)) = f.obj cf
f.hom (df.f (nt.obj (≅.fwd bidirAdjunction) dcL,cR cf)) φ =
  (f.hom cf φ) , (f.hom cf (dc.† (prl dcL,cR) φ))
f.hom-id' (df.f (nt.obj (≅.fwd bidirAdjunction) dcL,cR cf)) x =
  ×ext (f.hom-id' cf x) (map= (f.hom cf) (dc.†-id (prl dcL,cR) x) • f.hom-id' cf x)
f.hom-m∘' (df.f (nt.obj (≅.fwd bidirAdjunction) dcL,cR cf)) ψ φ =
  ×ext
    (f.hom-m∘' cf ψ φ)
    (map= (f.hom cf) (dc.†-m∘ (prl dcL,cR) ψ φ) • f.hom-m∘' cf (dc.† (prl dcL,cR) φ) (dc.† (prl dcL,cR) ψ))
df.hom-† (nt.obj (≅.fwd bidirAdjunction) dcL,cR cf) φ =
  ×ext refl (map= (f.hom cf) (dc.††-eq (prl dcL,cR) φ))

-- dcg : L' → L , ch : R → R' ; now show that (bidir ch) ∘ cf> ∘ dcg = (ch ∘ cf ∘ dcg)>
nt.hom' (≅.fwd bidirAdjunction) dcg,ch =
  λ= cf => dfunctorext (functorext (pair-ext refl (λi= x => λi= y => λ= φ => ×ext
    refl
    (map= (f.hom (prr dcg,ch)) (map= (f.hom cf) (sym (df.hom-† (prl dcg,ch) φ))))
  )))

-- dcf : L → bidir R. Now create functor dcf< : L → R
f.obj (nt.obj (≅.bck bidirAdjunction) dcL,cR dcf) = df.obj dcf
f.hom (nt.obj (≅.bck bidirAdjunction) dcL,cR dcf) φ = prl (df.hom dcf φ)
f.hom-id' (nt.obj (≅.bck bidirAdjunction) dcL,cR dcf) x = map= prl (df.hom-id' dcf x)
f.hom-m∘' (nt.obj (≅.bck bidirAdjunction) dcL,cR dcf) ψ φ = map= prl (df.hom-m∘' dcf ψ φ)

-- dcg : L' → L , ch : R → R' ; now show that ch ∘ dcf< ∘ dcg = ((bidir ch) ∘ dcf ∘ dcg)<
nt.hom' (≅.bck bidirAdjunction) dcg,ch = λ= dcf => functorext refl



≅.src-id bidirAdjunction = nt-ext (λ= dcL,cR => λ= cf => functorext refl)

≅.tgt-id bidirAdjunction = nt-ext (λ= dcL,cR => λ= dcf => dfunctorext (functorext (pair-ext
    refl
    (λi= x => λi= y => λ= φ => ×ext refl
      --prove that a †-functor to bidir maps φ to (f φ, f † φ)
      (map= prl (df.hom-† dcf φ))
    )
  )))
