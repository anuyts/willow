module willow.cat.Adjunction where

open import willow.cat.Category public
open import willow.cat.Sets public
open import willow.cat.Isomorphism public
open import willow.cat.HomFunctor public
open import willow.cat.Product public

_⊣_ : ∀{ℓo ℓh} → {cL cR : Cat ℓo ℓh} → (cf : cL ++> cR) → (cg : cR ++> cL) → Set (ℓo ⊔ lsuc ℓh)
_⊣_ {ℓo}{ℓh} {cL}{cR} cf cg =
  Iso (cExp (cOp cL c× cR) (cSet ℓh))
  (cHom cR c∘ cmap× (c-op cf) (c-id cR))
  (cHom cL c∘ cmap× (c-id (cOp cL)) cg)
  --(cHom cR c∘ (c-op cf c∘ c-prl (cOp cL) cR c⊠ c-prr (cOp cL) cR))
  --(cHom cL c∘ (c-prl (cOp cL) cR c⊠ cg c∘ c-prr (cOp cL) cR))
--\dashv
--an adjunction F ⊣ G is a natural equivalence Hom(F-, -) nt≅ Hom(-, G-)


{-
record _⊣_ {ℓo ℓh} {cL cR : Cat ℓo ℓh} (fl : cL ++> cR) (fr : cR ++> cL) : Set (ℓo ⊔ ℓh) where
  no-eta-equality
  field
    iso : {l : c.Obj cL} → {r : c.Obj cR} → Iso (cSet ℓh) (c.Hom cL l (f.obj fr r)) (c.Hom cR (f.obj fl l) r)

  {-
  record Hom (l : c.Obj cL) (r : c.Obj cR) : Set ℓh where
    no-eta-equality
    field
      left : c.Hom cR (f.obj fl l) r
      right : c.Hom cL l (f.obj fr r)
      left-eq : left == ≅.bck iso right
      right-eq : ≅.fwd iso left == right
  -}

  field
    fwd-m∘ : {l' l : c.Obj cL} → {r : c.Obj cR} → (ξ : c.Hom cL l (f.obj fr r)) → (φ : c.Hom cL l' l)
      → ≅.fwd iso (cL $ ξ m∘ φ) == cR $ (≅.fwd iso ξ) m∘ (f.hom fl φ)
    bck-m∘ : {l : c.Obj cL} → {r r' : c.Obj cR} → (φ : c.Hom cR r r') → (ξ : c.Hom cR (f.obj fl l) r)
      → ≅.bck iso (cR $ φ m∘ ξ) == cL $ (f.hom fr φ) m∘ (≅.bck iso ξ)

  coreturn : (fl c∘ fr) nt→ c-id cR
  coreturn = record
    { obj = λ r → ≅.fwd iso (c.id cL (f.obj fr r))
    ; hom = λ {r}{r'} φ →
          {- Idea
             φ ∘ fwd (id Rr)
             = fwd bck (φ ∘ fwd (id Rr))
             = fwd (Rφ ∘ bck fwd (id Rr))
             = fwd (Rφ ∘ id Rr)
             = fwd (Rφ)
             = fwd (id Rr' ∘ Rφ)
             = fwd (id Rr') ∘ LRφ
          -}
      via (cR $ φ m∘ ≅.fwd iso (c.id cL (f.obj fr r))) $ refl •
      via ≅.fwd iso (≅.bck iso (cR $ φ m∘ ≅.fwd iso (c.id cL (f.obj fr r)))) $ happly (sym (≅.tgt-id iso)) _ •
      via ≅.fwd iso (cL $ f.hom fr φ m∘ ≅.bck iso (≅.fwd iso (c.id cL (f.obj fr r)))) $ map= (≅.fwd iso) (bck-m∘ _ _) •
      via ≅.fwd iso (cL $ f.hom fr φ m∘ c.id cL (f.obj fr r)) $
        map= (λ ξ → ≅.fwd iso (cL $ f.hom fr φ m∘ ξ)) (happly (≅.src-id iso) _) •
      via ≅.fwd iso (f.hom fr φ) $ map= (≅.fwd iso) (c.m∘runit cL) •
      via ≅.fwd iso (cL $ c.id cL (f.obj fr r') m∘ f.hom fr φ) $ map= (≅.fwd iso) (sym (c.m∘lunit cL)) • 
      via (cR $ ≅.fwd iso (c.id cL (f.obj fr r')) m∘ f.hom fl (f.hom fr φ)) $ fwd-m∘ _ _ •
      refl
    }
  return : c-id cL nt→ (fr c∘ fl)
  return = record
    { obj = λ l → ≅.bck iso (c.id cR (f.obj fl l))
    ; hom = λ {l'}{l} φ →
          {- Idea
             RLφ ∘ bck (id Ll')
             = bck (Lφ ∘ id Ll')
             = bck (Lφ)
             = bck (id Ll ∘ Lφ)
             = bck (fwd bck (id Ll) ∘ Lφ)
             = bck fwd (bck (id Ll) ∘ φ)
             = bck (id Ll) ∘ φ
          -}
      via (cL $ f.hom fr (f.hom fl φ) m∘ ≅.bck iso (c.id cR (f.obj fl l'))) $ refl •
      via ≅.bck iso (cR $ f.hom fl φ m∘ c.id cR (f.obj fl l')) $ sym (bck-m∘ _ _) •
      via ≅.bck iso (f.hom fl φ) $ map= (≅.bck iso) (c.m∘runit cR) •
      via ≅.bck iso (cR $ c.id cR _ m∘ f.hom fl φ) $ map= (≅.bck iso) (sym (c.m∘lunit cR)) •
      via ≅.bck iso (cR $ ≅.fwd iso (≅.bck iso (c.id cR _)) m∘ f.hom fl φ) $
        map= (λ ξ → ≅.bck iso (cR $ ξ m∘ f.hom fl φ)) (sym (happly (≅.tgt-id iso) _)) •
      via ≅.bck iso (≅.fwd iso (cL $ ≅.bck iso (c.id cR _) m∘ φ)) $ map= (≅.bck iso) (sym (fwd-m∘ _ _)) •
      via (cL $ ≅.bck iso (c.id cR _) m∘ φ) $ happly (≅.src-id iso) _ •
      refl
    }
    --left-id : {!!} nt∘ (fl c∘nt η) == {!!} --nt-id fl

module ⊣ = _⊣_
-}

{-
record
  { iso = λ {l r} → record
    { fwd = ?
    ; bck = ?
    ; src-id = ?
    ; tgt-id = ?
    }
  ; fwd-m∘ = ?
  ; bck-m∘ = ?
  }
-}
