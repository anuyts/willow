module willow.cat.Zigzag.Tools where

open import willow.cat.RawZigzag public
open import willow.cat.Zigzag.Definition public

---------------auxiliary-----------------------------------------

zz-nil : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x : c.Obj c} → Zigzag c x x
zz-nil = mk-zz rz-refl

pre-zz> : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} (zz : Zigzag c x y) {z : c.Obj c} (φ : c.Hom c y z) → Zigzag c x z
pre-zz> {ℓo}{ℓh}{c}{x} = elim-zz
  (λ y → {z : c.Obj c} (φ : c.Hom c y z) → Zigzag c x z)
  (λ y rz φ → mk-zz (rz rz> φ))
  (λ y rz rz' p → λi= z => λ= φ => eq-zz (zz-cong-fwd p))

_zz>_ : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} (zz : Zigzag c x y) (φ : c.Hom c y z) → Zigzag c x z
zz zz> φ = pre-zz> zz φ

pre-zz< : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} (zz : Zigzag c x y) {z : c.Obj c} (φ : c.Hom c z y) → Zigzag c x z
pre-zz< {ℓo}{ℓh}{c}{x} = elim-zz
  (λ y → {z : c.Obj c} (φ : c.Hom c z y) → Zigzag c x z)
  (λ y rz φ → mk-zz (rz rz< φ))
  (λ y rz rz' p → λi= z => λ= φ => eq-zz (zz-cong-bck p))

_zz<_ : ∀ {ℓo ℓh} {c : Cat ℓo ℓh} {x y z : c.Obj c} (zz : Zigzag c x y) (φ : c.Hom c z y) → Zigzag c x z
zz zz< φ = pre-zz< zz φ

infixl 10 _zz>_ _zz<_

zz-fwd : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c x y → Zigzag c x y
zz-fwd φ = mk-zz (rz-fwd φ)

zz-bck : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → c.Hom c y x → Zigzag c x y
zz-bck φ = mk-zz (rz-bck φ)
