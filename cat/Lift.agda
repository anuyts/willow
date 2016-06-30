module willow.cat.Lift where

open import willow.cat.Category

cLift : ∀{α β γ δ} → Cat α β → Cat (α ⊔ γ) (β ⊔ δ)
c.Obj (cLift {α}{β}{γ}{δ} c) = Lift {α}{γ} (c.Obj c)
c.Hom (cLift {α}{β}{γ}{δ} c) x y = Lift{β}{δ} (c.Hom c (lower x) (lower y))
c.id (cLift {α}{β}{γ}{δ} c) x = lift (c.id c (lower x))
c.comp (cLift {α}{β}{γ}{δ} c) (lift ψ) (lift φ) = lift (c $ ψ m∘ φ)
c.m∘assoc' (cLift {α}{β}{γ}{δ} c) = map= lift (c.m∘assoc' c)
c.m∘lunit' (cLift {α}{β}{γ}{δ} c) = map= lift (c.m∘lunit' c)
c.m∘runit' (cLift {α}{β}{γ}{δ} c) = map= lift (c.m∘runit' c)

c-lift : ∀{α β γ δ} → {c : Cat α β} → c ++> cLift{_}{_}{γ}{δ} c
f.obj c-lift = lift
f.hom c-lift = lift
f.hom-id' c-lift x = refl
f.hom-m∘' c-lift ψ φ = refl

c-lower : ∀{α β γ δ} → {c : Cat α β} → cLift{_}{_}{γ}{δ} c ++> c
f.obj c-lower = lower
f.hom c-lower = lower
f.hom-id' c-lower x = refl
f.hom-m∘' c-lower ψ φ = refl
