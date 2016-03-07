module willow.cat.Sets where

open import willow.cat.Category public
open import willow.cat.Product public
--open import willow.cat.Monoidal public

cSet : (α : Level) → Cat (lsuc α) α
cSet α = record
  { Obj = Set α
  ; Hom = λ X Y → (X → Y)
  ; id = λ X → (λ x → x)
  ; comp = λ g f → g ∘ f
  ; m∘assoc = λ {W} {X} {Y} {Z} {h} {g} {f} → ∘assoc f g h
  ; m∘lunit = λ {X} {Y} {f} → λ= x => refl
  ; m∘runit = λ {X} {Y} {f} → λ= x => refl
  }

cSet× : ∀ {α} → cSet α c× cSet α ++> cSet α
cSet× = record
  { obj = λ Xs → prl Xs × prr Xs
  ; hom = λ fs → λ xs → (prl fs) (prl xs) , (prr fs) (prr xs)
  ; hom-id = λ Xs → refl
  ; hom-m∘ = λ gs fs → refl
  }

{-
mcSet : (α : Level) → MCat (lsuc α) α
mcSet α = record
  { mc:cat = cSet α
  ; mc:ops = record
    { monoid:1 = Lift ⊤
    ; monoid:⊗ = cSet×
    }
  ; mc:laws = record
    { monoid:assoc = mcSet:assoc
    ; monoid:lunit = mcSet:lunit
    ; monoid:runit = mcSet:runit
    }
  } where
  mcSet:assoc = record
      { m-fwd = mcSet:assoc:fwd
      ; m-bck = mcSet:assoc:bck 
      ; m-src-id = nt-ext (λi= [X,Y],Z => funext (λ {((x , y), z) → refl}))
      ; m-tgt-id = nt-ext (λi= [X,Y],Z => funext (λ {(x ,(y , z)) → refl}))
      } where
      mcSet:assoc:fwd = record -- a natural transformation over functors with domain (cSet c× cSet) c× cSet
        { ntobj = λ {[X,Y],Z} → λ [x,y],z → prl (prl [x,y],z) , (prr (prl [x,y],z) , prr [x,y],z)
        ; nthom = λ {[X,Y],Z [X,Y],Z' [f,g],h} → funext (λ {((x , y), z) → refl})
        }
      mcSet:assoc:bck = record
        { ntobj = λ {[X,Y],Z} → λ x,[y,z] → (prl x,[y,z] , prl (prr x,[y,z])) , prr (prr x,[y,z])
        ; nthom = λ {[X,Y],Z [X,Y],Z' [f,g],h} → funext (λ {(x ,(y , z)) → refl})
        }
  mcSet:lunit = record
      { m-fwd = mcSet:lunit:fwd
      ; m-bck = mcSet:lunit:bck 
      ; m-src-id = nt-ext (λi= X => funext (λ {(lift unit , x) → refl}))
      ; m-tgt-id = nt-ext (λi= X => λ= x => refl)
      } where
      mcSet:lunit:fwd = record
        { ntobj = λ {X} → prr
        ; nthom = λ {X Y f} → funext (λ {(lift unit , x) → refl})
        }
      mcSet:lunit:bck = record
        { ntobj = λ {X} x → (lift unit , x)
        ; nthom = λ {X Y f} → λ= x => refl
        }
  mcSet:runit = record
      { m-fwd = mcSet:runit:fwd
      ; m-bck = mcSet:runit:bck 
      ; m-src-id = nt-ext (λi= X => funext (λ {(x , lift unit) → refl}))
      ; m-tgt-id = nt-ext (λi= X => λ= x => refl)
      } where
      mcSet:runit:fwd = record
        { ntobj = λ {X} → prl
        ; nthom = λ {X Y f} → funext (λ {(x , lift unit) → refl})
        }
      mcSet:runit:bck = record
        { ntobj = λ {X} x → (x , lift unit)
        ; nthom = λ {X Y f} → λ= x => refl
        }
-}
