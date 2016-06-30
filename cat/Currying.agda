open import willow.cat.Category public
open import willow.cat.Product public

module willow.cat.Currying where

c-curried : ∀{ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} → (cA : Cat ℓoA ℓhA) → (cB : Cat ℓoB ℓhB) → (cC : Cat ℓoC ℓhC)
  → (cA c× cB ++> cC) → (cA ++> cExp cB cC)
f.obj (c-curried cA cB cC cf) a = cf c∘ (cConst a c⊠ c-id cB)
nt.obj (f.hom (c-curried cA cB cC cf) {a}{a'} α) b = f.hom cf (α , (c.id cB b))
nt.hom (f.hom (c-curried cA cB cC cf) {a}{a'} α) {b}{b'} β =
  sym (f.hom-m∘ cf (c.id cA a' , β) (α , c.id cB b))
  • map= (f.hom cf) (×ext
      (c.m∘lunit cA • sym (c.m∘runit cA))
      (c.m∘runit cB • sym (c.m∘lunit cB))
    )
  • f.hom-m∘ cf (α , c.id cB b') (c.id cA a , β)
f.hom-id (c-curried cA cB cC cf) a = nt-ext (λ= b => f.hom-id cf (a , b))
f.hom-m∘ (c-curried cA cB cC cf) α' α = nt-ext (λ= b => (
    map= (f.hom cf) (×ext refl (sym (c.m∘lunit cB))) • f.hom-m∘ cf (α' , c.id cB b) (α , c.id cB b)
  ))
