open import willow.cat.Category public
open import willow.basic.UIP.HeteroIdentity public
open import willow.cat.Presheaf public
open import willow.cat.OfElements public
import willow.cat.CwF.Psh
import willow.cat.CwF.HasSums

module willow.cat.CwF.Psh.HasSums {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.CwF.Psh ℓtm cW public
open willow.cat.CwF.HasSums cwfPsh public
--open willow.cat.CwF.HasSums.HasSums cwfPsh public

TΣ : {Γ : Ctx} → (A : Ty Γ) → (B : Ty (Γ „ A)) → Ty Γ
f.obj (TΣ A B) (w , γ) = Sum λ(a : f.obj A (w , γ)) → f.obj B (w , (γ , a))
f.hom (TΣ A B) {w₂ , γ₂}{w₁ , γ₁} (ρ , γ₂ρ=γ₁) (a , b) =
  (f.hom A (ρ , γ₂ρ=γ₁) a) , f.hom B (ρ , (trust (pair-hext γ₂ρ=γ₁ (
    (hdmap= (λ γ' → λ p → f.hom A {w₂ , γ₂}{w₁ , γ'} (ρ , p) a) γ₂ρ=γ₁) =aph= huip hrefl
  )))) b
f.hom-id' (TΣ {Γ} A B) (w , γ) = funext λ{(a , b) → pair-hext (happly (f.hom-id A (w , γ)) a) (
    via f.hom B {_}{w , (γ , f.hom A (c.id (c∫ Γ) (w , γ)) a)} (c.id cW w , trustMe) b $ hrefl h•
    via f.hom B {_}{w , (γ , a)} (c.id (c∫ (Γ „ A)) (w , (γ , a))) b $
      (hdmap= (λ a' p → f.hom B {_}{w , (γ , a')} (c.id cW w , p) b) (happly (f.hom-id A (w , γ)) a)) =aph= huip hrefl h•
    to-heter (happly (f.hom-id B (w , (γ , a))) b)
  )}
f.hom-m∘' (TΣ {Γ} A B) {w₃ , γ₃}{w₂ , γ₂}{w₁ , γ₁} (ρ , γ₂ρ=γ₁)(σ , γ₃σ=γ₂) = funext (λ {(a , b) → {!!} })
{-{!funext λ{(a , b) → pair-hext
    {!!}
    {!!}
  }!}-}

pshHasSums : HasSums
HasSums.TΣ pshHasSums A B = {!!}
HasSums.TΣ[]' pshHasSums A B = {!!}
HasSums.tpair pshHasSums a b = {!!}
HasSums.tprl pshHasSums ab = {!!}
HasSums.tprr pshHasSums ab = {!!}
HasSums.tprlβ' pshHasSums a b = {!!}
HasSums.tprrβ' pshHasSums a b = {!!}
HasSums.tpairη' pshHasSums ab = {!!}
HasSums.tpair[]' pshHasSums a b = {!!}
HasSums.tprl[]' pshHasSums ab = {!!}
HasSums.tprr[]' pshHasSums ab = {!!}
