module willow.basic.Propositional where

open import willow.basic.Basic
open import willow.basic.Function

-- proposition --------------------------------------------------

Is¶ : ∀{α} → (A : Set α) → Set α
Is¶ A = {a b : A} → a == b

-- ¶ is backslash P or altgr+7 on USMacintosh

-- propositional truncation -------------------------------------

private
  record ¶' {α} (A : Set α) : Set α where
    constructor propo'
    field
      val : A

¶ : ∀ {α} → (A : Set α) → Set α
¶ = ¶'

` : ∀ {α} → {A : Set α} → A → ¶ A
` a = propo' a

postulate ¶¶ : ∀ {α} → (A : Set α) → Is¶ (¶ A)

elim¶ : ∀ {α β} → {A : Set α} → {B : Set β} → (f : A → B) → Is¶ B → ¶ A → B
elim¶ f t (propo' a) = f a

map¶ : ∀ {α β} → {A : Set α} → {B : Set β} → (f : A → B) → (¶ A → ¶ B)
map¶ {α}{β}{A}{B} f = elim¶ (` ∘ f) (¶¶ B)

postulate β¶ : ∀ {α β} → {A : Set α} → {B : Set β} → (f : A → B) → (f= : Is¶ B) → (a a' : A) → map= (elim¶ f f=) (¶¶ A {` a} {` a'}) == f= {f a}{f a'}

prod¶ : ∀{α β} → {A : Set α} → {B : Set β} → Is¶ B → Is¶ (A → B)
prod¶ {α}{β}{A}{B} is¶B = λ {f} {g} → funext (λ a → is¶B)

--appl¶ : ∀{α β} → {A : Set α} → {B : Set β} → ¶(A → B) → (¶ A → ¶ B)
--appl¶ {α}{β}{A}{B} pf pa = {!!}

bind¶ : ∀{α β} → {A : Set α} → {B : Set β} → ¶ A → (A → ¶ B) → ¶ B
bind¶ {α}{β}{A}{B} pa f = elim¶ f (¶¶ B) pa

syntax bind¶ pa (λ x → pb) = x ← pa ,¶ pb
infixr 1 bind¶

-- properties ------------------------------------

is¶⊥ : Is¶ ⊥
is¶⊥ {()}

is¶⊤ : Is¶ ⊤
is¶⊤ {unit}{unit} = refl

is¶Lift : ∀ {α β} → {A : Set α} → Is¶ A → Is¶ (Lift {α}{β} A)
is¶Lift {A} is¶A {lift a} {lift b} = map= lift is¶A

is¶× : ∀{α β} → {A : Set α} → {B : Set β} → Is¶ A → Is¶ B → Is¶ (A × B)
is¶× {_}{_}{A}{B} p q {a , a'} {b , b'} = map= (λ x → _ , x) q • map= (λ x → x , _) p

is¶→ : ∀{α β} → {A : Set α} → {B : A → Set β} → ((a : A) → Is¶ (B a)) → Is¶ ((a : A) → B a)
is¶→ {_}{_} {A}{B} p {f}{g} = λ= a => p a
is¶i→ : ∀{α β} → {A : Set α} → {B : A → Set β} → ((a : A) → Is¶ (B a)) → Is¶ ({a : A} → B a)
is¶i→ {_}{_} {A}{B} p {f}{g} = λi= a => p a

syntax is¶→ (λ a → s) = λ¶ a => s
syntax is¶i→ (λ a → s) = λ¶i a => s

--dependent pairs and stuff--------------------------

pair¶ext : ∀{α β} → {A : Set α} → {B : A → Set β} → {a a' : A} → (p : a == a') → {b : B a} → {b' : B a'} → ((a : A) → Is¶ (B a)) → (a , b) == (a' , b')
pair¶ext {_}{_} {A}{B} {a}{.a} refl {b}{b'} is¶B = map= (_,_ a) (is¶B a)
