module willow.cat.Category where

open import willow.basic.Basic public
open import willow.basic.Function public
open import willow.basic.UIP public

record Cat (α β : Level) : Set (lsuc (α ⊔ β)) where
  no-eta-equality
  constructor mkCat
  field
    Obj : Set α
    Hom : (x : Obj) → (y : Obj) → Set β
    id : (x : Obj) → Hom x x
    comp : {x y z : Obj} → (ψ : Hom y z) → (φ : Hom x y) → Hom x z
    m∘assoc' : {w x y z : Obj} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x} → comp (comp ψ ξ) φ == comp ψ (comp ξ φ)
    m∘lunit' : {x y : Obj} → {φ : Hom x y} → comp (id y) φ == φ
    m∘runit' : {x y : Obj} → {φ : Hom x y} → comp φ (id x) == φ
  m∘assoc : {w x y z : Obj} → {ψ : Hom y z} → {ξ : Hom x y} → {φ : Hom w x} → comp (comp ψ ξ) φ == comp ψ (comp ξ φ)
  m∘assoc = trust m∘assoc'
  m∘lunit : {x y : Obj} → {φ : Hom x y} → comp (id y) φ == φ
  m∘lunit = trust m∘lunit'
  m∘runit : {x y : Obj} → {φ : Hom x y} → comp φ (id x) == φ
  m∘runit = trust m∘runit'
module c = Cat

_$_m∘_ : ∀{α β} → (c : Cat α β) → {x y z : c.Obj c} → c.Hom c y z → c.Hom c x y → c.Hom c x z
c $ ψ m∘ φ = c.comp c ψ φ

Candid-obj : ∀{α β γ δ} → (cA : Cat α β) → (cB : Cat γ δ) → Set _
Candid-obj cA cB = c.Obj cA → c.Obj cB
Candid-hom : ∀{α β γ δ} → (cA : Cat α β) → (cB : Cat γ δ) → (objpart : Candid-obj cA cB) → Set _
Candid-hom cA cB objpart = {x y : c.Obj cA} → (φ : c.Hom cA x y) → c.Hom cB (objpart x) (objpart y)
Candid-objhom : ∀{α β γ δ} → (cA : Cat α β) → (cB : Cat γ δ) → Set _
Candid-objhom cA cB = Sum λ (objpart : Candid-obj cA cB) → Candid-hom cA cB objpart
Candid-hom-id : ∀{α β γ δ} → (cA : Cat α β) → (cB : Cat γ δ) → (objpart : Candid-obj cA cB) → (hompart : Candid-hom cA cB objpart) → Set _
Candid-hom-id cA cB objpart hompart = (x : c.Obj cA) → hompart(c.id cA x) == c.id cB (objpart x)
Candid-hom-m∘ : ∀{α β γ δ} → (cA : Cat α β) → (cB : Cat γ δ) → (objpart : Candid-obj cA cB) → (hompart : Candid-hom cA cB objpart) → Set _
Candid-hom-m∘ cA cB objpart hompart = {x y z : c.Obj cA} → (ψ : c.Hom cA y z) → (φ : c.Hom cA x y) → hompart(cA $ ψ m∘ φ) == cB $ hompart ψ m∘ hompart φ

record _++>_ {α β γ δ} (cA : Cat α β) (cB : Cat γ δ) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  no-eta-equality --- since you want to prove equality of functors, best have eta-equality.
  constructor mk-f
  field
    obj : Candid-obj cA cB
    hom : Candid-hom cA cB obj
    hom-id' : Candid-hom-id cA cB obj hom
    hom-m∘' : Candid-hom-m∘ cA cB obj hom
  hom-id : Candid-hom-id cA cB obj hom
  hom-id x = trust (hom-id' x)
  hom-m∘ : Candid-hom-m∘ cA cB obj hom
  hom-m∘ ψ φ = trust (hom-m∘' ψ φ)
infix 1 _++>_
module f = _++>_

_c∘_ : ∀{α β γ δ ε ζ} → {cA : Cat α β} → {cB : Cat γ δ} → {cC : Cat ε ζ} → (cB ++> cC) → (cA ++> cB) → (cA ++> cC)
f.obj (cg c∘ cf) = f.obj cg ∘ f.obj cf
f.hom (cg c∘ cf) = f.hom cg ∘ f.hom cf
f.hom-id' (_c∘_ {α}{β}{γ}{δ}{ε}{ζ} {cA}{cB}{cC} cg cf) a =
  via f.hom cg (c.id cB (f.obj cf a)) $ map= (f.hom cg) (f.hom-id' cf a) • f.hom-id' cg (f.obj cf a)
f.hom-m∘' (_c∘_ {α}{β}{γ}{δ}{ε}{ζ} {cA}{cB}{cC} cg cf) ψ φ =
  map= (f.hom cg) (f.hom-m∘' cf ψ φ) • f.hom-m∘' cg (f.hom cf ψ) (f.hom cf φ)
infixl 10 _c∘_

c-id : ∀{α β} → (cA : Cat α β) → (cA ++> cA)
f.obj (c-id cA) = idf
f.hom (c-id cA) = idf
f.hom-id' (c-id cA) x = refl
f.hom-m∘' (c-id cA) ψ φ = refl

cConst : ∀{α β γ δ} → {cA : Cat α β} → {cB : Cat γ δ} → (b : c.Obj cB) → (cA ++> cB)
f.obj (cConst b) x = b
f.hom (cConst {cB = cB} b) φ = c.id cB b
f.hom-id' (cConst b) x = refl
f.hom-m∘' (cConst {cB = cB} b) ψ φ = sym (c.m∘lunit' cB)

functorext : ∀{ℓoA}{ℓhA}{ℓoB}{ℓhB} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → {cf cg : cA ++> cB}
  → (Candid-objhom cA cB $ (f.obj cf , f.hom cf) == (f.obj cg , f.hom cg))
  → cf == cg
functorext {ℓoA}{ℓoB}{ℓhA}{ℓhB} {cA}{cB} {mk-f obj hom hom-id hom-m∘}{mk-f .obj .hom ghom-id ghom-m∘} refl =
  let eq-hom-id : hom-id == ghom-id
      eq-hom-id = trust (λ¶ a => uip)
      eq-hom-m∘ : Candid-hom-m∘ cA cB obj hom $ hom-m∘ == ghom-m∘
      eq-hom-m∘ = trust (λ¶i x => λ¶i y => λ¶i z => λ¶ ψ => λ¶ φ => uip)
  in (map= (mk-f obj hom) eq-hom-id) =ap= eq-hom-m∘
  
{-
functorext {α}{β}{γ}{δ} {cA}{cB} {cf}{cg} p =
  let mk-f' = uncurry (mk-f {cA = cA}{cB = cB})
      mk-f'' = λ objhompart → uncurry (mk-f' objhompart)
      Properties : Candid-objhom cA cB → Set _
      Properties objhompart =
        (Candid-hom-id cA cB (prl objhompart) (prr objhompart)) ×
        (Candid-hom-m∘ cA cB (prl objhompart) (prr objhompart))
      --properties : (obj)
      --lemma1 : mk-f'(obj cf , hom cf) == (tra (λ objhompart → {!!}) / (sym p)) (mk-f'(obj cg , hom cg))
      --lemma1 = {!!}
  in via cf $ refl •
     via mk-f' (f.obj cf , f.hom cf) (f.hom-id' cf) (f.hom-m∘' cf) $ refl •
     via mk-f'' (f.obj cf , f.hom cf) (f.hom-id' cf , f.hom-m∘' cf) $ refl •
     via
       mk-f'' (f.obj cg , f.hom cg) ( (tra Properties / p) (f.hom-id' cf , f.hom-m∘' cf) )
       $ (mapd=func-left mk-f'' p (f.hom-id' cf , f.hom-m∘' cf)) •
     via mk-f'' (f.obj cg , f.hom cg) (f.hom-id' cg , f.hom-m∘' cg)
       $ (map=
         (mk-f'' (f.obj cg , f.hom cg))
         {(tra Properties / p) (f.hom-id' cf , f.hom-m∘' cf)}
         {f.hom-id' cg , f.hom-m∘' cg}
         (is¶× (λ¶i x => uip) (λ¶i x => λ¶i y => λ¶i z => λ¶i ψ => λ¶i φ => uip))
       ) •
     via mk-f' (f.obj cg , f.hom cg) (f.hom-id' cg) (f.hom-m∘' cg) $ refl •
     via cg $ refl • refl
-}

Candid-ntobj : ∀{α β γ δ} → {cA : Cat α β} → {cB : Cat γ δ} → (cf cg : cA ++> cB) → Set (δ ⊔ α)
Candid-ntobj {α}{β}{γ}{δ} {cA}{cB} cf cg = (x : c.Obj cA) → c.Hom cB (f.obj cf x) (f.obj cg x)

Candid-nthom : ∀{α β γ δ} → {cA : Cat α β} → {cB : Cat γ δ} → (cf cg : cA ++> cB) → (objpart : Candid-ntobj cf cg) → Set (α ⊔ β ⊔ δ)
Candid-nthom {α}{β}{γ}{δ} {cA}{cB} cf cg objpart = {x y : c.Obj cA} → (φ : c.Hom cA x y) → (cB $ (f.hom cg φ) m∘ (objpart x)) == (cB $ (objpart y) m∘ (f.hom cf φ))

record _nt→_ {α β γ δ} {cA : Cat α β} {cB : Cat γ δ} (cf cg : cA ++> cB) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  no-eta-equality
  constructor mk-nt
  field
    obj : Candid-ntobj cf cg
      --{x : Obj cA} → Hom cB (obj cf x) (obj cg x)
    hom' : Candid-nthom cf cg obj
      --{x y : Obj cA} → {φ : Hom cA x y} → (cB $ (hom cg φ) m∘ ntobj) == (cB $ ntobj m∘ (hom cf φ))
  hom : Candid-nthom cf cg obj
  hom φ = trust (hom' φ)
infix 1 _nt→_
module nt = _nt→_

nt-ext : ∀{α β γ δ}
  → {cA : Cat α β} → {cB : Cat γ δ}
  → {cf cg : cA ++> cB} → {nta ntb : cf nt→ cg}
  → (p : (Candid-ntobj cf cg $ nt.obj nta == nt.obj ntb))
  → (nta == ntb)
nt-ext {ℓoA}{ℓhA}{ℓoB}{ℓhB} {cA}{cB} {cf}{cg} {mk-nt obj ahom}{mk-nt .obj bhom} refl =
  map= (mk-nt obj) (trust (λ¶i x => λ¶i y => λ¶ φ => uip))

{-
nt-ext {α} {β} {γ} {δ} {cA} {cB} {cf} {cg} {nta} {ntb} p =
  via nta $ refl •
  via
    record
      { ntobj = (ntobj nta)
      ; nthom = tra (Candid-nthom cf cg) / (sym p) of (nthom ntb)
      }
    $ (map= (mk-nt (ntobj nta)) (λi= x => λi= y => λi= φ => uip)) •
  via ntb $ mapd=func-right mk-nt p (nthom ntb) •
  refl
-}

nt-id : ∀{α β γ δ} → {cA : Cat α β} → {cB : Cat γ δ} → (cf : cA ++> cB) → (cf nt→ cf)
nt.obj (nt-id {cB = cB} cf) x = c.id cB (f.obj cf x)
nt.hom' (nt-id {cB = cB} cf) φ = via (f.hom cf φ) $ c.m∘runit' cB • sym (c.m∘lunit' cB)

_nt∘_ : ∀{α β γ δ} → {cA : Cat α β} → {cB : Cat γ δ} → {cf cg ch : cA ++> cB} → (ntb : cg nt→ ch) → (nta : cf nt→ cg) → (cf nt→ ch)
nt.obj (_nt∘_ {cB = cB}{cf}{cg}{ch} ntb nta) x = c.comp cB {f.obj cf x}{f.obj cg x}{f.obj ch x} (nt.obj ntb x) (nt.obj nta x)
nt.hom' (_nt∘_ {cB = cB}{cf}{cg}{ch} ntb nta) {x}{y} φ =
    via (cB $ (f.hom ch φ) m∘ (cB $ (nt.obj ntb x) m∘ (nt.obj nta x))) $ refl •
    via (cB $ (cB $ (f.hom ch φ) m∘ (nt.obj ntb x)) m∘ (nt.obj nta x)) $ sym (c.m∘assoc' cB) •
    via (cB $ (cB $ (nt.obj ntb y) m∘ (f.hom cg φ)) m∘ (nt.obj nta x)) $ map= (λ ψ → cB $ ψ m∘ (nt.obj nta x)) (nt.hom' ntb φ) •
    via (cB $ (nt.obj ntb y) m∘ (cB $ (f.hom cg φ) m∘ (nt.obj nta x))) $ c.m∘assoc' cB •
    via (cB $ (nt.obj ntb y) m∘ (cB $ (nt.obj nta y) m∘ (f.hom cf φ))) $ map= (λ ψ → cB $ (nt.obj ntb y) m∘ ψ) (nt.hom' nta φ) •
    via (cB $ (cB $ (nt.obj ntb y) m∘ (nt.obj nta y)) m∘ (f.hom cf φ)) $ sym (c.m∘assoc' cB) •
    refl

nt∘assoc : ∀ {α β γ δ} → {cA : Cat α β} → {cB : Cat γ δ} → {cf cg ch ck : cA ++> cB} → {ntc : ch nt→ ck} → {ntb : cg nt→ ch} → {nta : cf nt→ cg} → (ntc nt∘ ntb) nt∘ nta == ntc nt∘ (ntb nt∘ nta)
nt∘assoc {α}{β}{γ}{δ} {cA}{cB} {cf}{cg}{ch}{ck} {ntc}{ntb}{nta} =
  nt-ext (λ= x => c.m∘assoc' cB)

_nt∘c_ : ∀ {ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → {cC : Cat ℓoC ℓhC} → {cf cg : cB ++> cC} → (nt : cf nt→ cg) → (ck : cA ++> cB) → (cf c∘ ck nt→ cg c∘ ck)
nt.obj (nt nt∘c ck) x = nt.obj nt (f.obj ck x)
nt.hom' (nt nt∘c ck) φ = nt.hom' nt (f.hom ck φ)
infixl 11 _nt∘c_

_c∘nt_ : ∀ {ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} → {cA : Cat ℓoA ℓhA} → {cB : Cat ℓoB ℓhB} → {cC : Cat ℓoC ℓhC} → (ck : cB ++> cC) → {cf cg : cA ++> cB} → (nt : cf nt→ cg) → (ck c∘ cf nt→ ck c∘ cg)
nt.obj (_c∘nt_ ck {cf}{cg} nt) x = f.hom ck (nt.obj nt x)
nt.hom' (_c∘nt_ ck {cf}{cg} nt) φ =
     {- Idee:
     (k ∘ g)(φ) ∘ k(nt(x))
     := k(g(φ)) ∘ k(nt(x))
     = k(g(φ) ∘ nt(x))
     = k(nt(y) ∘ f(φ))
     = k(nt(y)) ∘ k(f(φ))
     := k(nt(y)) ∘ (k ∘ f)(φ)
     -}
    sym (f.hom-m∘' ck (f.hom cg φ) (nt.obj nt _)) •
    map= (f.hom ck) (nt.hom' nt φ) •
    f.hom-m∘' ck (nt.obj nt _) (f.hom cf φ)
infixl 11 _c∘nt_

cExp : ∀{ℓoA ℓhA ℓoB ℓhB} → (cA : Cat ℓoA ℓhA) → (cB : Cat ℓoB ℓhB) → Cat (ℓoA ⊔ ℓhA ⊔ ℓoB ⊔ ℓhB) (ℓoA ⊔ ℓhA ⊔ ℓoB ⊔ ℓhB)
Cat.Obj (cExp cA cB) = cA ++> cB
Cat.Hom (cExp cA cB) = _nt→_
Cat.id (cExp cA cB) = nt-id
Cat.comp (cExp cA cB) = _nt∘_
Cat.m∘assoc' (cExp cA cB) = nt-ext (λ= x => c.m∘assoc' cB)
Cat.m∘lunit' (cExp cA cB) = nt-ext (λ= x => c.m∘lunit' cB)
Cat.m∘runit' (cExp cA cB) = nt-ext (λ= x => c.m∘runit' cB)

c⊥ : Cat lzero lzero
Cat.Obj c⊥ = ⊥
Cat.Hom c⊥ ()
Cat.id c⊥ ()
Cat.comp c⊥ {}
Cat.m∘assoc' c⊥ {}
Cat.m∘lunit' c⊥ {}
Cat.m∘runit' c⊥ {}

c⊥elim : ∀{α β} → {c : Cat α β} → (c⊥ ++> c)
f.obj c⊥elim ()
f.hom c⊥elim {}
f.hom-id' c⊥elim ()
f.hom-m∘' c⊥elim {}
