module willow.cat.Locpath.Tools where

open import willow.cat.RawZigzag public
open import willow.cat.Locpath.Definition public

---------------auxiliary-----------------------------------------

lp-nil : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x : c.Obj c} → Locpath c x x
lp-nil = mk-lp rz-refl

pre-lp> : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} (lp : Locpath c x y) {z : c.Obj c} (φ : c.Hom c y z) → Locpath c x z
pre-lp> {ℓo}{ℓh}{c}{x} = elim-lp
  (λ y → {z : c.Obj c} (φ : c.Hom c y z) → Locpath c x z)
  (λ y rz φ → mk-lp (rz rz> φ))
  (λ y rz rz' p → λi= z => λ= φ => eq-lp (lp-cong-fwd p))

_lp>_ : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} (lp : Locpath c x y) (φ : c.Hom c y z) → Locpath c x z
lp lp> φ = pre-lp> lp φ

pre-lp< : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} (lp : Locpath c x y) {z : c.Obj c} (φ : c.Hom c z y) → Locpath c x z
pre-lp< {ℓo}{ℓh}{c}{x} = elim-lp
  (λ y → {z : c.Obj c} (φ : c.Hom c z y) → Locpath c x z)
  (λ y rz φ → mk-lp (rz rz< φ))
  (λ y rz rz' p → λi= z => λ= φ => eq-lp (lp-cong-bck p))

_lp<_ : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} (lp : Locpath c x y) (φ : c.Hom c z y) → Locpath c x z
lp lp< φ = pre-lp< lp φ

infixl 10 _lp>_ _lp<_

lp-fwd : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c x y → Locpath c x y
lp-fwd φ = mk-lp (rz-fwd φ)

lp-bck : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c y x → Locpath c x y
lp-bck φ = mk-lp (rz-bck φ)
