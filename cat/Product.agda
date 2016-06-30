module willow.cat.Product where

open import willow.cat.Category
open import willow.basic.Basic

_c×_ : ∀{ℓoL ℓhL ℓoR ℓhR} → (cL : Cat ℓoL ℓhL) → (cR : Cat ℓoR ℓhR) → Cat (ℓoL ⊔ ℓoR) (ℓhL ⊔ ℓhR)
c.Obj (cL c× cR) = c.Obj cL × c.Obj cR
c.Hom (cL c× cR) x y = (c.Hom cL (prl x) (prl y)) × (c.Hom cR (prr x) (prr y))
c.id (cL c× cR) x = (c.id cL (prl x) , c.id cR (prr x))
c.comp (cL c× cR) ψ φ = (cL $ (prl ψ) m∘ (prl φ) , cR $ (prr ψ) m∘ (prr φ))
c.m∘assoc' (cL c× cR) {ψ = ψ , ψ'} {ξ , ξ'} {φ , φ'} =
    via ( cL $ (cL $ ψ m∘ ξ) m∘ φ , cR $ (cR $ ψ' m∘ ξ') m∘ φ' ) $ refl •
    via ( cL $ ψ m∘ (cL $ ξ m∘ φ) , cR $ (cR $ ψ' m∘ ξ') m∘ φ' ) $ map= (λ x → x , _) (c.m∘assoc' cL) •
    via ( cL $ ψ m∘ (cL $ ξ m∘ φ) , cR $ ψ' m∘ (cR $ ξ' m∘ φ') ) $ map= (λ x → _ , x) (c.m∘assoc' cR) •
    refl
c.m∘lunit' (cL c× cR) {φ = φ , φ'} = map= (λ x → x , _) (c.m∘lunit' cL) • map= (λ x → _ , x) (c.m∘lunit' cR)
c.m∘runit' (cL c× cR) {φ = φ , φ'} = map= (λ x → x , _) (c.m∘runit' cL) • map= (λ x → _ , x) (c.m∘runit' cR)
infixr 4 _c×_

c×intro : ∀ {α β γ δ ε ζ} → {cA : Cat ε ζ} → (cL : Cat α β) → (cR : Cat γ δ) → (cA ++> cL) → (cA ++> cR) → (cA ++> (cL c× cR))
f.obj (c×intro cL cR cf cg) x = (f.obj cf x) , (f.obj cg x)
f.hom (c×intro cL cR cf cg) φ = (f.hom cf φ) , (f.hom cg φ)
f.hom-id' (c×intro cL cR cf cg) x = map= (λ x → x , _) (f.hom-id' cf x) • map= (λ x → _ , x) (f.hom-id' cg x)
f.hom-m∘' (c×intro cL cR cf cg) ψ φ = map= (λ x → x , _) (f.hom-m∘' cf ψ φ) • map= (λ x → _ , x) (f.hom-m∘' cg ψ φ)
_c⊠_ : ∀ {α β γ δ ε ζ} → {cA : Cat ε ζ} → {cL : Cat α β} → {cR : Cat γ δ} → (cA ++> cL) → (cA ++> cR) → (cA ++> (cL c× cR))
_c⊠_ = c×intro _ _
infixr 4 _c⊠_

c-prl : ∀{α β γ δ} → (cL : Cat α β) → (cR : Cat γ δ) → (cL c× cR ++> cL)
f.obj (c-prl cL cR) = prl
f.hom (c-prl cL cR) = prl
f.hom-id' (c-prl cL cR) x = refl
f.hom-m∘' (c-prl cL cR) ψ φ = refl

c-prr : ∀{α β γ δ} → (cL : Cat α β) → (cR : Cat γ δ) → (cL c× cR ++> cR)
f.obj (c-prr cL cR) = prr
f.hom (c-prr cL cR) = prr
f.hom-id' (c-prr cL cR) x = refl
f.hom-m∘' (c-prr cL cR) ψ φ = refl

c×-assoc-fwd : ∀ {α β γ δ ε ζ} → (cL : Cat α β) → (cM : Cat γ δ) → (cR : Cat ε ζ) -> (cL c× cM) c× cR ++> cL c× (cM c× cR)
c×-assoc-fwd cL cM cR = c×intro cL (cM c× cR) (c-prl cL cM c∘ c-prl (cL c× cM) cR) (c×intro cM cR (c-prr cL cM c∘ c-prl (cL c× cM) cR) (c-prr (cL c× cM) cR))
--(c-prl c∘ c-prl) c⊠ ((c-prr c∘ c-prl) c⊠ c-prr)

cmap× : ∀{ℓoL ℓhL ℓoR ℓhR ℓoL' ℓhL' ℓoR' ℓhR'}
  → {cL : Cat ℓoL ℓhL} → {cR : Cat ℓoR ℓhR}
  → {cL' : Cat ℓoL' ℓhL'} → {cR' : Cat ℓoR' ℓhR'}
  → (cf : cL ++> cL') → (cg : cR ++> cR') → (cL c× cR) ++> (cL' c× cR')
f.obj (cmap× cf cg) = map× (f.obj cf) (f.obj cg)
f.hom (cmap× cf cg) = map× (f.hom cf) (f.hom cg)
f.hom-id' (cmap× cf cg) x = ×ext (f.hom-id' cf (prl x)) (f.hom-id' cg (prr x))
f.hom-m∘' (cmap× cf cg) ψ φ = ×ext (f.hom-m∘' cf (prl ψ) (prl φ)) (f.hom-m∘' cg (prr ψ) (prr φ))

c-swap : ∀{ℓoA ℓhA ℓoB ℓhB} {cA : Cat ℓoA ℓhA} {cB : Cat ℓoB ℓhB} → cA c× cB ++> cB c× cA
f.obj c-swap (a , b) = b , a
f.hom c-swap (α , β) = β , α
f.hom-id' c-swap (a , b) = refl
f.hom-m∘' c-swap (α' , β') (α , β) = refl
