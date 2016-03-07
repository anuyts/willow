module willow.cat.Top where

--open import willow.cat.Monoidal public
open import willow.cat.Category public

c⊤ : Cat lzero lzero
c⊤ = record
  { Obj = ⊤
  ; Hom = λ x y → ⊤
  ; id = λ x → unit
  ; comp = λ ψ φ → unit
  ; m∘assoc = refl
  ; m∘lunit = λ {x y} → λ { {unit} → refl }
  ; m∘runit = λ {x y} → λ { {unit} → refl }
  }

c⊤intro : ∀{α β} → {c : Cat α β} → (c ++> c⊤)
c⊤intro = record
  { obj = λ _ → unit
  ; hom = λ {x} {y} _ → unit
  ; hom-id = λ x → refl
  ; hom-m∘ = λ {x} {y} {z} ψ φ → refl
  }

c⊤universal : ∀{α β} → {c : Cat α β} → {cf cg : c ++> c⊤} → (cf == cg)
c⊤universal {α}{β} {c} {cf}{cg} = functorext (pair-ext (λ¶ x => is¶⊤) (λ¶i x => λ¶i y => λ¶ φ => is¶⊤))

{-
mc⊤ : MCat lzero lzero
mc⊤ = record
  { mc:cat = c⊤
  ; mc:ops = record
    { monoid:1 = unit
    ; monoid:⊗ = c⊤intro
    }
  ; mc:laws = record
    { monoid:assoc = mc⊤:assoc
    ; monoid:lunit = mc⊤:lunit
    ; monoid:runit = mc⊤:runit
    }
  } where
    mc⊤:assoc = record
        { m-fwd = record
            { ntobj = unit
            ; nthom = refl
            }
        ; m-bck = record
            { ntobj = unit
            ; nthom = refl
            }
        ; m-src-id = refl
        ; m-tgt-id = nt-ext refl
        }
    mc⊤:lunit = record
        { m-fwd = record
            { ntobj = unit
            ; nthom = refl
            }
        ; m-bck = record
            { ntobj = unit
            ; nthom = refl
            }
        ; m-src-id = refl
        ; m-tgt-id = nt-ext refl
        }
    mc⊤:runit = record
        { m-fwd = record
            { ntobj = unit
            ; nthom = refl
            }
        ; m-bck = record
            { ntobj = unit
            ; nthom = refl
            }
        ; m-src-id = refl
        ; m-tgt-id = nt-ext refl
        }
-}
