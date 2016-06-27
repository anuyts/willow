module willow.basic.Function where

open import willow.basic.Identity public
open import willow.basic.Coproduct public
open import willow.basic.Sum public
--open import willow.basic.Basic public

--former-------------------------------------

Fun : ∀{ℓA ℓB} → (A : Set ℓA) → (B : Set ℓB) → Set (ℓB ⊔ ℓA)
Fun A B = A → B

--identity----------------------------------

idf : ∀ {α} → {X : Set α} → X → X
idf x = x

--composition-------------------------------

_∘_ : ∀ {α β γ} → {A : Set α} → {B : Set β} → {C : Set γ} → (B → C) → (A → B) → (A → C)
g ∘ f = λ a → g (f a)

infixl 10 _∘_

--funext-----------------------------------

postulate funext : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : (a : A) → B a} → ((a : A) → (f a == g a)) → f == g

happly : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : (a : A) → B a} → f == g → ((a : A) → (f a == g a))
happly refl = λ a → refl

postulate βfunext : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : (a : A) → B a} → (happly ∘ funext) == idf{_}{(a : A) → (f a == g a)}

postulate ηfunext : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : (a : A) → B a} → (funext ∘ happly) == idf{_}{f == g}

postulate funexti : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : {a : A} → B a} → ((a : A) → (f {a} == g {a})) → _==_ {_} { {a : A} → B a } f g

happlyi : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : {a : A} → B a} → _==_ {_} { {a : A} → B a } f g → ((a : A) → (f {a} == g {a}))
happlyi refl = λ a → refl

postulate βfunexti : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : {a : A} → B a} → (happlyi ∘ funexti) == idf{_}{(a : A) → (f {a} == g {a})}

postulate ηfunexti : ∀{α β} → {A : Set α} → {B : A → Set β} → {f g : {a : A} → B a} → (funexti ∘ happlyi) == idf{_}{_==_ {_} { {a : A} → B a } f g}

syntax funext (λ a → s) = λ= a => s
syntax funexti (λ a → s) = λi= a => s

--properties of composition----------------

∘assoc : {α β γ δ : Level} -> {A : Set α} -> {B : Set β} -> {C : Set γ} -> {D : Set δ} -> (f : A -> B) -> (g : B -> C) -> (h : C -> D) -> (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)
∘assoc f g h = funext (λ a -> refl)

∘leftUnity : {α β : Level} -> {A : Set α} -> {B : Set β} -> (f : A -> B) -> (idf ∘ f) == f
∘leftUnity f = funext (λ a -> refl)

∘rightUnity : {α β : Level} -> {A : Set α} -> {B : Set β} -> (f : A -> B) -> (f ∘ idf) == f
∘rightUnity f = funext (λ a -> refl)

--continuity-------------------------------

mapd=fwd : ∀ {α β} → {A : Set α} → {B : A → Set β} → (f : (a : A) → B a) → {a a' : A} → (p : a == a') → (tra B / p of (f a)) == (f a')
mapd=fwd f {a}{.a} refl = refl

mapd=bck : ∀ {α β} → {A : Set α} → {B : A → Set β} → (f : (a : A) → B a) → {a a' : A} → (p : a == a') → (f a) == (tra B / (sym p) of (f a'))
mapd=bck f {a}{.a} refl = refl

mapd=func-left : ∀ {α β γ} → {A : Set α} → {B : A → Set β} → {C : Set γ} → (f : (a : A) → B a → C) → {a a' : A} → (p : a == a') → (b : B a) → (f a b) == f a' (tra B / p of b)
mapd=func-left f {a}{.a} refl b = refl

mapd=func-right : ∀ {α β γ} → {A : Set α} → {B : A → Set β} → {C : Set γ} → (f : (a : A) → B a → C) → {a a' : A} → (p : a == a') → (b' : B a') → (f a (tra B / sym p of b')) == f a' b'
mapd=func-right f {a}{.a} refl b = refl

ap= : ∀ {ℓA ℓB} → {A : Set ℓA} → {B : Set ℓB} → {f f' : A → B} → (=f : f == f') → {a a' : A} → (=a : a == a') → (f a == f' a')
ap= refl refl = refl

_=ap=_ = ap=
infixl 20 _=ap=_

--transport of functions------------------

--trafun-lemma : ∀{τ α β} → {T : Set τ} → {A : T → Set α} → {B : T → Set β} → {t t' : T} → (f : A t → B t) → (p : t == t') → (a0 : A t') → (tra (λ s → A s → B s) / p of f) a0 == (tra B / p of f (tra A / (sym p) of a0))
--trafun-lemma {τ}{α}{β} {T}{A}{B} {t}{.t} f refl = happly refl -- a0 = refl
trafun-lemma : ∀{τ α β} → (T : Set τ) → (A : T → Set α) → (B : T → Set β) → {t t' : T} → (f : A t → B t) → (p : t == t') → (tra (λ s → A s → B s) / p of f) == (tra B / p) ∘ f ∘ (tra A / (sym p))
trafun-lemma {τ}{α}{β} T A B {t}{.t} f refl = refl

--coproduct-------------------------------

mapOR : ∀ {α β γ δ} → {A : Set α} → {B : Set β} → {C : Set γ} → {D : Set δ} → (f : A → C) → (g : B → D) → (A OR B) → (C OR D)
mapOR f g (inl a) = inl (f a)
mapOR f g (inr b) = inr (g b)

--match-------------------------------------

--case_of : ∀{α β} → {A : Set α} → (a : A) → {B : A → Set β} → ((x : A) → B x) → B a
case_of : ∀{α β} → {A : Set α} → (a : A) → {B : Set β} → (A → B) → B
case x of f = f x

case_return_of : ∀{α β} → {A : Set α} → (a : A) → (B : A → Set β) → ((x : A) → B x) → B a
case x return B of f = f x

--currying----------------------------------

uncurry : ∀{α β γ} → {A : Set α} → {B : A → Set β} → {C : (a : A) → B a → Set γ} → (f : (a : A) → (b : B a) → C a b) → (ab : Sum B) → C (prl ab) (prr ab)
uncurry {_}{_}{_} {A}{B}{C} f ab = f (prl ab) (prr ab)

--uncurry-eq : ∀{α β γ} → {A : Set α} → {B : A → Set β} → {C : (a : A) → B a → Set γ} → {f : (a : A) → (b : B a) → C a b} → {ab : Sum B} → 
