module willow.cat.Enriched where

open import willow.cat.Monoidal public

record ECat (α : Level) {β γ} (M : MCat β γ) : Set ((lsuc α) ⊔ β ⊔ γ) where
  field
    e:Obj : Set α
    e:Hom : e:Obj → e:Obj → mc:Obj M
    e:m-id : {x : e:Obj} → mc:Hom M (mc:1 M) (e:Hom x x)
    e:m-comp : {x y z : e:Obj} → mc:Hom M (mc: M $ (e:Hom y z) ⊗ (e:Hom x y)) (e:Hom x z)
    e:m∘assoc : {w x y z : e:Obj} →
      (mc: M $ e:m-comp{w}{x}{z} m∘ (fhom (mc:⊗ M) (e:m-comp{x}{y}{z} , mc:m-id M)))
      == mc: M $ (mc: M $ e:m-comp{w}{y}{z} m∘ fhom (mc:⊗ M) (mc:m-id M , e:m-comp{w}{x}{y})) m∘ (ntobj (m-fwd (mc:assoc M)))
    --in short, this says that (ψ e:m∘ ξ) e:m∘ φ = [ψ e:m∘ (ξ e:m∘ φ)] mc:m∘ associativity-of-⊗
