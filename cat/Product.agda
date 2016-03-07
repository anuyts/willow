module aken.cat.Product where

open import aken.cat.Category
open import aken.basic.Basic

_c×_ : ∀{ℓoL ℓhL ℓoR ℓhR} → (cL : Cat ℓoL ℓhL) → (cR : Cat ℓoR ℓhR) → Cat (ℓoL ⊔ ℓoR) (ℓhL ⊔ ℓhR)
cL c× cR = record
  { Obj = c.Obj cL × c.Obj cR
  ; Hom = λ x y → (c.Hom cL (prl x) (prl y)) × (c.Hom cR (prr x) (prr y))
  ; id = λ x → (c.id cL (prl x) , c.id cR (prr x))
  ; comp = λ ψ φ → (cL $ (prl ψ) m∘ (prl φ) , cR $ (prr ψ) m∘ (prr φ))
  ; m∘assoc = λ { {_} {_} {_} {_} {ψ , ψ'} {ξ , ξ'} {φ , φ'} → 
    via ( cL $ (cL $ ψ m∘ ξ) m∘ φ , cR $ (cR $ ψ' m∘ ξ') m∘ φ' ) $ refl •
    via ( cL $ ψ m∘ (cL $ ξ m∘ φ) , cR $ (cR $ ψ' m∘ ξ') m∘ φ' ) $ map= (λ x → x , _) (c.m∘assoc cL) •
    via ( cL $ ψ m∘ (cL $ ξ m∘ φ) , cR $ ψ' m∘ (cR $ ξ' m∘ φ') ) $ map= (λ x → _ , x) (c.m∘assoc cR) •
    refl
    }
  ; m∘lunit = λ { {_} {_} {φ , φ'} → map= (λ x → x , _) (c.m∘lunit cL) • map= (λ x → _ , x) (c.m∘lunit cR) }
  ; m∘runit = λ { {_} {_} {φ , φ'} → map= (λ x → x , _) (c.m∘runit cL) • map= (λ x → _ , x) (c.m∘runit cR) }
  }
infixr 4 _c×_

c×intro : ∀ {α β γ δ ε ζ} → {cA : Cat ε ζ} → (cL : Cat α β) → (cR : Cat γ δ) → (cA ++> cL) → (cA ++> cR) → (cA ++> (cL c× cR))
c×intro cL cR cf cg = record
  { obj = λ x → (f.obj cf x) , (f.obj cg x)
  ; hom = λ φ → (f.hom cf φ) , (f.hom cg φ)
  ; hom-id = λ x → map= (λ x → x , _) (f.hom-id cf x) • map= (λ x → _ , x) (f.hom-id cg x)
  ; hom-m∘ = λ ψ φ → map= (λ x → x , _) (f.hom-m∘ cf ψ φ) • map= (λ x → _ , x) (f.hom-m∘ cg ψ φ)
  }
_c⊠_ : ∀ {α β γ δ ε ζ} → {cA : Cat ε ζ} → {cL : Cat α β} → {cR : Cat γ δ} → (cA ++> cL) → (cA ++> cR) → (cA ++> (cL c× cR))
_c⊠_ = c×intro _ _
infixr 4 _c⊠_

c-prl : ∀{α β γ δ} → (cL : Cat α β) → (cR : Cat γ δ) → (cL c× cR ++> cL)
c-prl cL cR = record
  { obj = prl
  ; hom = prl
  ; hom-id = λ x → refl
  ; hom-m∘ = λ ψ φ → refl
  }

c-prr : ∀{α β γ δ} → (cL : Cat α β) → (cR : Cat γ δ) → (cL c× cR ++> cR)
c-prr cL cR = record
  { obj = prr
  ; hom = prr
  ; hom-id = λ x → refl
  ; hom-m∘ = λ ψ φ → refl
  }

c×-assoc-fwd : ∀ {α β γ δ ε ζ} → (cL : Cat α β) → (cM : Cat γ δ) → (cR : Cat ε ζ) -> (cL c× cM) c× cR ++> cL c× (cM c× cR)
c×-assoc-fwd cL cM cR = c×intro cL (cM c× cR) (c-prl cL cM c∘ c-prl (cL c× cM) cR) (c×intro cM cR (c-prr cL cM c∘ c-prl (cL c× cM) cR) (c-prr (cL c× cM) cR))
--(c-prl c∘ c-prl) c⊠ ((c-prr c∘ c-prl) c⊠ c-prr)

cmap× : ∀{ℓoL ℓhL ℓoR ℓhR ℓoL' ℓhL' ℓoR' ℓhR'}
  → {cL : Cat ℓoL ℓhL} → {cR : Cat ℓoR ℓhR}
  → {cL' : Cat ℓoL' ℓhL'} → {cR' : Cat ℓoR' ℓhR'}
  → (cf : cL ++> cL') → (cg : cR ++> cR') → (cL c× cR) ++> (cL' c× cR')
cmap× {_}{_}{_}{_}{_}{_}{_}{_} {cL}{cR}{cL'}{cR'} cf cg = record
  { obj = map× (f.obj cf) (f.obj cg)
  ; hom = map× (f.hom cf) (f.hom cg)
  ; hom-id = λ x → ×ext (f.hom-id cf (prl x)) (f.hom-id cg (prr x))
  ; hom-m∘ = λ ψ φ → ×ext (f.hom-m∘ cf (prl ψ) (prl φ)) (f.hom-m∘ cg (prr ψ) (prr φ))
  }
