module aken.cat.Lift where

open import aken.cat.Category

cLift : ∀{α β γ δ} → Cat α β → Cat (α ⊔ γ) (β ⊔ δ)
cLift {α}{β}{γ}{δ} c = record
  { Obj = Lift {α}{γ} (c.Obj c)
  ; Hom = λ x y → Lift{β}{δ} (c.Hom c (lower x) (lower y))
  ; id = λ x → lift (c.id c (lower x))
  ; comp = λ ψ φ → lift (c $ lower ψ m∘ lower φ)
  ; m∘assoc = map= lift (c.m∘assoc c)
  ; m∘lunit = map= lift (c.m∘lunit c)
  ; m∘runit = map= lift (c.m∘runit c)
  }

c-lift : ∀{α β γ δ} → {c : Cat α β} → c ++> cLift{_}{_}{γ}{δ} c
c-lift {α}{β}{γ}{δ} {c} = record
  { obj = lift
  ; hom = lift
  ; hom-id = λ x → refl
  ; hom-m∘ = λ ψ φ → refl
  }

c-lower : ∀{α β γ δ} → {c : Cat α β} → cLift{_}{_}{γ}{δ} c ++> c
c-lower {α}{β}{γ}{δ} {c} = record
  { obj = lower
  ; hom = lower
  ; hom-id = λ x → refl
  ; hom-m∘ = λ ψ φ → refl
  }
