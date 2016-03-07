module aken.cat.Isomorphism where

open import aken.cat.Category public
open import aken.basic.Basic public

record Iso {α β} (c : Cat α β) (x y : c.Obj c) : Set β where
  no-eta-equality
  constructor mk≅
  field
    fwd : c.Hom c x y
    bck : c.Hom c y x
    src-id : (c $ bck m∘ fwd) == c.id c x
    tgt-id : (c $ fwd m∘ bck) == c.id c y
module ≅ = Iso --cong

IsIso : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → {x y : c.Obj c} → (φ : c.Hom c x y) → Set ℓh
IsIso {_}{_} c {x}{y} φ = Sum λ (η : Iso c x y) → ≅.fwd η == φ

_$_i∘_ : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → {x y z : c.Obj c} → (ψ : Iso c y z) → (φ : Iso c x y) → Iso c x z
c $ ψ i∘ φ = record
  { fwd = c $ ≅.fwd ψ m∘ ≅.fwd φ
  ; bck = c $ ≅.bck φ m∘ ≅.bck ψ
  ; src-id =
    c.m∘assoc c •
    map= (λ ξ → c $ ≅.bck φ m∘ ξ) (sym (c.m∘assoc c)) •
    map= (λ ξ → c $ ≅.bck φ m∘ (c $ ξ m∘ ≅.fwd φ)) (≅.src-id ψ) •
    map= (λ ξ → c $ ≅.bck φ m∘ ξ) (c.m∘lunit c) •
    ≅.src-id φ
  ; tgt-id =
    c.m∘assoc c •
    map= (λ ξ → c $ ≅.fwd ψ m∘ ξ) (sym (c.m∘assoc c)) •
    map= (λ ξ → c $ ≅.fwd ψ m∘ (c $ ξ m∘ ≅.bck ψ)) (≅.tgt-id φ) •
    map= (λ ξ → c $ ≅.fwd ψ m∘ ξ) (c.m∘lunit c) •
    ≅.tgt-id ψ
  }

i-id : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → (x : c.Obj c) → Iso c x x
i-id c x = record
  { fwd = c.id c x
  ; bck = c.id c x
  ; src-id = c.m∘lunit c
  ; tgt-id = c.m∘lunit c
  }

≅ext : ∀{ℓo ℓh} → {c : Cat ℓo ℓh} → {x y : c.Obj c} → {φ ψ : Iso c x y} → (≅.fwd φ == ≅.fwd ψ) → φ == ψ
≅ext {_}{_} {c} {x}{y} {mk≅ φfwd φbck φsrc-id φtgt-id}{mk≅ .φfwd ψbck ψsrc-id ψtgt-id} refl =
  let eq-bck : φbck == ψbck
      --φbck = φbck ∘ id = φbck ∘ (φ ∘ ψbck) = (φbck ∘ φ) ∘ ψbck = id ∘ ψbck = ψbck
      eq-bck =
        sym (c.m∘runit c) •
        map= (λ ξ → c $ φbck m∘ ξ) (sym ψtgt-id) •
        sym (c.m∘assoc c) •
        map= (λ ξ → c $ ξ m∘ ψbck) φsrc-id •
        c.m∘lunit c
      weak≅ext : {α β : Iso c x y} → (≅.fwd α == ≅.fwd β) → (≅.bck α == ≅.bck β) → α == β
      weak≅ext = λ { {mk≅ fwd bck _ _} {mk≅ .fwd .bck _ _} refl refl → (map= (mk≅ fwd bck) uip) =ap= uip }
  in weak≅ext refl eq-bck

is¶IsIso : ∀{ℓo ℓh} → {c : Cat ℓo ℓh} → {x y : c.Obj c} → (φ : c.Hom c x y) → Is¶ (IsIso c φ)
is¶IsIso {ℓo}{ℓh} {c} {x}{y} φ {≅φ}{≅φ'} =
  let eq-iso : prl ≅φ == prl ≅φ'
      eq-iso = ≅ext (prr ≅φ • sym (prr ≅φ'))
  in pair¶ext eq-iso (λ a → uip)

i-inv : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → {x y : c.Obj c} → (φ : Iso c x y) → Iso c y x
i-inv c φ = record
  { fwd = ≅.bck φ
  ; bck = ≅.fwd φ
  ; src-id = ≅.tgt-id φ
  ; tgt-id = ≅.src-id φ
  }

mapIso : ∀{ℓoA ℓhA ℓoB ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → (cf : cA ++> cB) → {x y : c.Obj cA} → (η : Iso cA x y) → Iso cB (f.obj cf x) (f.obj cf y)
mapIso {_}{_}{_}{_} {cA}{cB} cf {x}{y} η = record
  { fwd = f.hom cf (≅.fwd η)
  ; bck = f.hom cf (≅.bck η)
  ; src-id = sym (f.hom-m∘ cf (≅.bck η) (≅.fwd η)) • map= (f.hom cf) (≅.src-id η) • f.hom-id cf x
  ; tgt-id = sym (f.hom-m∘ cf (≅.fwd η) (≅.bck η)) • map= (f.hom cf) (≅.tgt-id η) • f.hom-id cf y
  }

inv-id : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → (x : c.Obj c) → (η : Iso c x x) → (≅.fwd η == c.id c x) → (≅.bck η == c.id c x)
inv-id c x (mk≅ .(c.id c x) bck src-id tgt-id) refl = sym (c.m∘runit c) • src-id

inv-m∘ : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → {x y z : c.Obj c}
  → (ψ : Iso c y z) → (φ : Iso c x y) → (η : Iso c x z)
  → (≅.fwd η == c $ ≅.fwd ψ m∘ ≅.fwd φ) → (≅.bck η == c $ ≅.bck φ m∘ ≅.bck ψ)
inv-m∘ c ψ φ (mk≅ .(c $ ≅.fwd ψ m∘ ≅.fwd φ) ηbck ηsrc ηtgt) refl =
  map= ≅.bck (((mk≅ (c $ ≅.fwd ψ m∘ ≅.fwd φ) ηbck ηsrc ηtgt) == c $ ψ i∘ φ) ∋ ≅ext refl)

{-
record
  { fwd = ?
  ; bck = ?
  ; src-id = ?
  ; tgt-id = ?
  }
-}
