module aken.cat.Categories where

open import aken.cat.Category public
--open import aken.cat.Monoidal public
open import aken.cat.Top public
open import aken.cat.Lift public
open import aken.cat.Product public

cCat : (α β : Level) → Cat (lsuc (α ⊔ β)) (α ⊔ β)
cCat α β = record
  { Obj = Cat α β
  ; Hom = λ cA cB → cA ++> cB
  ; id = c-id
  ; comp = _c∘_
  ; m∘assoc = λ {cA cB cC cD ch cg cf} → functorext (pair-ext refl refl)
  ; m∘lunit = λ {cA cB cf} → functorext (pair-ext refl refl)
  ; m∘runit = λ {cA cB cf} → functorext (pair-ext refl refl)
  }

cCat× : ∀{α β} → cCat α β c× cCat α β ++> cCat α β
cCat× = record
  { obj = λ cs → prl cs c× prr cs
  ; hom = λ {cAs}{cBs} cfs → c×intro (prl cBs) (prr cBs) (prl cfs c∘ (c-prl (prl cAs) (prr cAs))) (prr cfs c∘ (c-prr (prl cAs) (prr cAs)))
  ; hom-id = λ x → refl
  ; hom-m∘ = λ {cAs cBs cCs} cfs cgs → functorext (pair-ext refl refl)
  }

{-
mcCat : (α β : Level) → MCat (lsuc (α ⊔ β)) (α ⊔ β)
mcCat α β = record
  { mc:cat = cCat α β
  ; mc:ops = record
    { monoid:1 = cLift c⊤
    ; monoid:⊗ = cCat×
    }
  ; mc:laws = record
    { monoid:assoc = {!!} --mcCat:assoc
    ; monoid:lunit = record
      { m-fwd = record
          { ntobj = λ {cX} → c-prr (cLift c⊤) cX
          ; nthom = functorext (pair-ext refl refl)
          }
      ; m-bck = record
          { ntobj = λ {cX} → c×intro (cLift c⊤) cX (c-lift c∘ c⊤intro) c-id
          ; nthom = functorext (pair-ext refl refl)
          }
      ; m-src-id =
        nt-ext (
          λi= cX =>
          functorext {cA = (cLift c⊤) c× cX}{cB = (cLift c⊤) c× cX} (
            pair-ext (funext λ {(lift unit , x) → refl}) {!!}
          )
        )
      ; m-tgt-id = nt-ext (λi= cX => functorext {cA = cX}{cB = cX} (pair-ext refl refl))
      }
    ; monoid:runit = {!!} --mcCat:runit
    }
  } where
{-  mcCat:assoc =
    let mcCat:assoc:fwd = record
          { ntobj = {!!}
          ; nthom = {!!}
          }
        mcCat:assoc:bck = record
          { ntobj = {!!}
          ; nthom = {!!}
          }
    in record
      { m-fwd = mcCat:assoc:fwd
      ; m-bck = mcCat:assoc:bck 
      ; m-src-id = {!!}
      ; m-tgt-id = {!!}
      } -}
{-  mcCat:runit = 
    let mcCat:runit:fwd = record
          { ntobj = c-prl
          ; nthom = functorext (pair-ext refl refl)
          }
        mcCat:runit:bck = record
          { ntobj = c-id c⊠ (c-lift c∘ c⊤intro)
          ; nthom = functorext (pair-ext refl refl)
          }
    in record
      { m-fwd = mcCat:runit:fwd
      ; m-bck = mcCat:runit:bck 
      ; m-src-id = nt-ext (λi= cX => functorext (pair-ext {!funext λ {(x , lift unit) → refl}!} {!!}))
      ; m-tgt-id = nt-ext (λi= cX => functorext (pair-ext {!refl!} {!!}))
      }

-}
-}
