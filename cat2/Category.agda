module willow.cat2.Category where

open import willow.basic.Basic public
open import willow.basic.Function renaming (id to idf) public
open import willow.basic.Preimage public

record CatStr {ℓo ℓh} (Obj : Set ℓo) (Mph : Set ℓh) : Set (ℓo ⊔ ℓh) where
  no-eta-equality
  
  field
    src : Mph → Obj
    tgt : Mph → Obj
  
  Hom : Obj → Obj → Set ℓh
  Hom x y = Mph ! (src ⊠ tgt) ↦ (x , y)

  traHom : {x x' : Obj} → (p : x == x') → {y y' : Obj} → (q : y == y') → Hom x y → Hom x' y'
  traHom = λ { {._}{._} refl {._}{._} refl φ → φ}
 
  field
    id : (x : Obj) → Hom x x
    comp : {x y z : Obj} → (ψ : Hom y z) → (φ : Hom x y) → Hom x z
    m∘lunit' : {x y : Obj} → {φ : Hom x y} → comp (id y) φ == φ
    m∘runit' : {x y : Obj} → {φ : Hom x y} → comp φ (id x) == φ
    m∘assoc' : {w x y z : Obj} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x} → comp (comp ψ ξ) φ == comp ψ (comp ξ φ)

  m-id : Obj → Mph
  m-id = λ x → out! (id x)
module cs = CatStr

--\l-2
_⇇_ = CatStr

record Cat (ℓo ℓh : Level) : Set (lsuc (ℓo ⊔ ℓh)) where
  no-eta-equality
  field
    Obj : Set ℓo
    Mph : Set ℓh
    catStr : Obj ⇇ Mph
module c {ℓo ℓh} (cX : Cat ℓo ℓh) where
  open Cat cX public
  open CatStr catStr public

record FunctorStr {ℓoA ℓhA ℓoB ℓhB}
       {ObjA : Set ℓoA} {MphA : Set ℓhA} (csA : ObjA ⇇ MphA)
       {ObjB : Set ℓoB} {MphB : Set ℓhB} (csB : ObjB ⇇ MphB)
       (fobj : ObjA → ObjB) (fmph : MphA → MphB) : Set (ℓoA ⊔ ℓhA ⊔ ℓoB ⊔ ℓhB) where
  no-eta-equality
  
  field
    fsrc : (φ : _) → fobj (cs.src csA φ) == cs.src csB (fmph φ)
    ftgt : (φ : _) → fobj (cs.tgt csA φ) == cs.tgt csB (fmph φ)
  
  fhom : {x y : ObjA} → (φ : cs.Hom csA x y) → cs.Hom csB (fobj x) (fobj y)
  fhom = λ {
    {._} {._} (in! φ)
      --→ tra (λ xy → MphB ! (cs.src csB ⊠ cs.tgt csB) ↦ xy) / ×ext (sym (fsrc φ)) (sym (ftgt φ)) of in! (fmph φ)
      → cs.traHom csB (sym (fsrc φ)) (sym (ftgt φ)) (in! (fmph φ))
    }
  
  field
    fid : (x : ObjA) → fhom (cs.id csA x) == cs.id csB (fobj x)
    fcomp : {x y z : ObjA} → (ψ : cs.Hom csA y z) → (φ : cs.Hom csA x y)
      → fhom (cs.comp csA ψ φ) == cs.comp csB (fhom ψ) (fhom φ)
module fs = FunctorStr

record _++>_ {ℓoA ℓhA ℓoB ℓhB} (cA : Cat ℓoA ℓhA) (cB : Cat ℓoB ℓhB) : Set (ℓoA ⊔ ℓhA ⊔ ℓoB ⊔ ℓhB) where
  no-eta-equality
  field
    fobj : c.Obj cA → c.Obj cB
    fmph : c.Mph cA → c.Mph cB
    fstr : FunctorStr (c.catStr cA) (c.catStr cB) fobj fmph

module f {ℓoA ℓhA ℓoB ℓhB} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} (cf : cA ++> cB) where
  open _++>_ cf public
  open FunctorStr fstr public
