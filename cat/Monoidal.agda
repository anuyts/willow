module aken.cat.Monoidal where

open import aken.cat.Category public
open import aken.cat.Product public
open import aken.cat.Isomorphism public
open import aken.basic.Basic public

record MCatOps {α β} (c : Cat α β) : Set (α ⊔ β) where
  no-eta-equality
  field
    monoid:1 : Obj c
    monoid:⊗ : (c c× c) ++> c

  [-⊗-]⊗- : (c c× c) c× c ++> c
  [-⊗-]⊗- = monoid:⊗ c∘ ((monoid:⊗ c∘ c-prl (c c× c) c) c⊠ c-prr (c c× c) c)
  -⊗[-⊗-] : c c× (c c× c) ++> c
  -⊗[-⊗-] = monoid:⊗ c∘ (c-prl c (c c× c) c⊠ (monoid:⊗ c∘ c-prr c (c c× c)))

  -⊗1 : c ++> c
  -⊗1 = monoid:⊗ c∘ (c×intro c c c-id (cConst monoid:1))

  1⊗- : c ++> c
  1⊗- = monoid:⊗ c∘ (c×intro c c (cConst monoid:1) c-id)
open MCatOps public

record MCatLaws {α β} {c : Cat α β} (ops : MCatOps c) : Set (α ⊔ β) where
  no-eta-equality
  field
    monoid:assoc : Iso (cExp ((c c× c) c× c) c) ([-⊗-]⊗- ops) ((-⊗[-⊗-] ops) c∘ c×-assoc-fwd c c c)
    monoid:lunit : Iso (cExp c c) (1⊗- ops) c-id
    monoid:runit : Iso (cExp c c) (-⊗1 ops) c-id
open MCatLaws public


--YOU NEED COHERENCE OF ASSOCIATOR AND UNITORS!!!



{-
record IsMonoidal {α β} (c : Cat α β) : Set (α ⊔ β) where
  no-eta-equality
  field
    monoid:1 : Obj c
    monoid:⊗ : (c c× c) ++> c

  [-⊗-]⊗- : (c c× c) c× c ++> c
  [-⊗-]⊗- = monoid:⊗ c∘ ((monoid:⊗ c∘ c-prl) c⊠ c-prr)
  -⊗[-⊗-] : c c× (c c× c) ++> c
  -⊗[-⊗-] = monoid:⊗ c∘ (c-prl c⊠ (monoid:⊗ c∘ c-prr))

  -⊗1 : c ++> c
  -⊗1 = monoid:⊗ c∘ (c-id c⊠ (cConst monoid:1))

  1⊗- : c ++> c
  1⊗- = monoid:⊗ c∘ ((cConst monoid:1) c⊠ c-id)

  field
    monoid:assoc : Iso (cExp ((c c× c) c× c) c) [-⊗-]⊗- (-⊗[-⊗-] c∘ c×-assoc-fwd)
    monoid:lunit : Iso (cExp c c) 1⊗- c-id
    monoid:runit : Iso (cExp c c) -⊗1 c-id
open IsMonoidal public
-}

--MCat = λ {α β} → Sum λ (c : Cat α β) → IsMonoidal c

record MCat (α β : Level) : Set (lsuc (α ⊔ β)) where
  no-eta-equality
  field
    mc:cat : Cat α β
    mc:ops : MCatOps mc:cat
    mc:laws : MCatLaws mc:ops
  mc:Obj = Obj mc:cat
  mc:Hom = Hom mc:cat
  mc:m-id = m-id mc:cat
  mc:m-cat = m-cat mc:cat
  mc:_$_m∘_ = mc:m-cat
  mc:m∘assoc = m∘assoc mc:cat
  mc:m∘lunit = m∘lunit mc:cat
  mc:m∘runit = m∘runit mc:cat
  mc:1 = monoid:1 mc:ops
  mc:⊗ = monoid:⊗ mc:ops
  mc:assoc = monoid:assoc mc:laws
  mc:lunit = monoid:lunit mc:laws
  mc:runit = monoid:runit mc:laws

  mc:_$_⊗_ : mc:Obj → mc:Obj → mc:Obj
  mc:_$_⊗_ x y = fobj (mc:⊗) (x , y)
open MCat public

{-
record
  { mc:cat = ?
  ; mc:monoidal = ?
  }

record
    { monoid:1 = ?
    ; monoid:⊗ = ?
    ; monoid:assoc = ?
    ; monoid:lunit = ?
    ; monoid:runit = ?
    }

    let fwd = record
          { ntobj = ?
          ; nthom = ?
          }
        bck = record
          { ntobj = ?
          ; nthom = ?
          }
    in record
      { m-fwd = fwd
      ; m-bck = bck 
      ; m-src-id = ?
      ; m-tgt-id = ?
      }
-}
