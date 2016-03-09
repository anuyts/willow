module willow.cat2.OmegaCategory where

open import willow.cat2.Category public
open import willow.basic.Basic public

record 2CatStr {ℓi ℓo ℓh}
  {Idx : Set ℓi} {Obj : Set ℓo} {Mph : Set ℓh}
  (csIO : Idx ⇇ Obj) (csOM : Obj ⇇ Mph) (csIM : Idx ⇇ Mph) : Set (ℓi ⊔ ℓo ⊔ ℓh) where
  no-eta-equality
  field
    fs-src : FunctorStr csIM csIO idf (cs.src csOM)
    fs-tgt : FunctorStr csIM csIO idf (cs.tgt csOM)
    fs-id : FunctorStr csIO csIM idf (cs.m-id csOM)
    {-
      i --x-> j --x'-> k
          |       |
          φ       φ'
          V       V
      i --y-> j --y'-> k
          |       |
          ψ       ψ'
          V       V
      i --z-> j --z'-> k
    -}

  csHomOM : (i j : Idx) → cs.Hom csIO i j ⇇ cs.Hom csIM i j
  csHomOM = λ i j → record
    { src = λ φ → cs.traHom csIO
      (sym (fs.fsrc fs-src (out! φ)) • map= prl (deduce! φ))
      (sym (fs.ftgt fs-src (out! φ)) • map= prr (deduce! φ))
      (in! (cs.src csOM (out! φ)))
    ; tgt = λ φ → cs.traHom csIO
      (sym (fs.fsrc fs-tgt (out! φ)) • map= prl (deduce! φ))
      (sym (fs.ftgt fs-tgt (out! φ)) • map= prr (deduce! φ))
      (in! (cs.tgt csOM (out! φ)))
    ; id = λ x → {!!} --cs.traHom (csHomOM i j) ? ? ?
      --{!cs.traHom csIM ? ? {!(in! (cs.id csOM (out! x)))!}!}
    ; comp = {!!}
    ; m∘lunit = {!!}
    ; m∘runit = {!!}
    ; m∘assoc = {!!}
    }

    {-
    exchange-law : {i j k : Idx} → {x y z : cs.Hom csIO i j} → {x' y' z' : cs.Hom csIO j k}
      → (φ : cs.Mph csOM (out! x) (out! y))
      → (ψ : cs.Mph csOM (out! y) (out! z))
      → (φ' : cs.Mph csOM (out! x') (out! y'))
      → (ψ' : cs.Mph csOM (out! y') (out! z'))
      → cs.comp csIM {i}{j}{k}
        {!!}
        {!!}
      == cs.comp csIM {i}{j}{k}
        {!!}
        {!!}
    -}

{-
record 2CatStr {ℓi ℓo ℓh}
  {Idx : Set ℓi} {Obj : Set ℓo} {Hom : Set ℓh}
  (csIO : CatStr Idx Obj) (csOH : CatStr Obj Hom) (csIH : CatStr Idx Hom) : Set (ℓi ⊔ ℓo ⊔ ℓh) where
  no-eta-equality
  field
    fs-src : FunctorStr csIH csIO idf (cs.src csOH)
    fs-tgt : FunctorStr csIH csIO idf (cs.tgt csOH)
    fs-id : FunctorStr csIO csIH idf (cs.id csOH)
    {-
      i --x-> j --x'-> k
          |       |
          φ       φ'
          V       V
      i --y-> j --y'-> k
          |       |
          ψ       ψ'
          V       V
      i --z-> j --z'-> k
    -}
    exchange-law : (φ ψ φ' ψ' : Hom) →
      {-let x : Obj
          x = cs.src csOH φ
          y : Obj
          y = cs.tgt csOH φ
          z : Obj
          z = cs.tgt csOH ψ
          x' : Obj
          x' = cs.src csOH φ'
          y' : Obj
          y' = cs.tgt csOH φ'
          z' : Obj
          z' = cs.tgt csOH ψ'
          i : Idx
          i = cs.src csIH φ
          j : Idx
          j = cs.tgt csIH φ
          k : Idx
          k = cs.tgt csIH φ'
      in-}
      (p : cs.src csOH ψ == cs.tgt csOH φ) → (p' : cs.src csOH ψ' == cs.tgt csOH φ') → (q : cs.src csIH φ' == cs.tgt csIH φ)
        → cs.comp csIH (cs.comp csOH ψ' φ' p') (cs.comp csOH ψ φ p) ({!? • ? • ?!})
        == cs.comp csOH
          (cs.comp csIH ψ' ψ (
            fs.fsrc fs-src ψ' • (map= (cs.src csIO) p') • sym (fs.fsrc fs-tgt φ') • q •
            fs.ftgt fs-tgt φ  • sym (map= (cs.tgt csIO) p) • sym (fs.ftgt fs-src ψ)
          ))
          (cs.comp csIH φ' φ q)
          {!!}
    --(p : cs.src csOH ψ == cs.tgt csOH φ) → (q : cs.src)

record Catω (ℓ : Level) : Set (lsuc ℓ) where
  no-eta-equality
  field
    Hom : Nat → Set ℓ
    catStr : (m n : Nat) → (m < n) → CatStr (Hom m) (Hom n)
-}
