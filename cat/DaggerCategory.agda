module willow.cat.DaggerCategory where

open import willow.cat.Zigzag public
open import willow.cat.Opposite public
open import willow.basic.Preimage public

record IsDCat {ℓo ℓh : Level} (c : Cat ℓo ℓh) : Set (ℓo ⊔ ℓh) where
  no-eta-equality
  field
    † : ∀{x y} → (φ : c.Hom c x y) → c.Hom c y x
    †-id : (x : c.Obj c) → † (c.id c x) == c.id c x
    †-m∘ : ∀{x y z} → (ψ : c.Hom c y z) → (φ : c.Hom c x y) → † (c $ ψ m∘ φ) == c $ († φ) m∘ († ψ)
    ††-eq : ∀{x y} (φ : c.Hom c x y) → † († φ) == φ

  c† : c ++> cOp c
  _++>_.obj c† = idf
  _++>_.hom c† φ = † φ
  _++>_.hom-id' c† x = †-id x
  _++>_.hom-m∘' c† ψ φ = †-m∘ ψ φ

  c††-eq : (c-op c†) c∘ c† == ≅.fwd (≅OpOp c)
  c††-eq = functorext (pair-ext refl (λi= x => λi= y => λ= φ => ††-eq φ))

record DCat (ℓo ℓh : Level) : Set (lsuc (ℓo ⊔ ℓh)) where
  no-eta-equality
  field
    cat : Cat ℓo ℓh
    isDCat : IsDCat cat

  open Cat cat public
  open IsDCat isDCat public

module dc = DCat

--isDaggerFunctor : ∀{ℓoA ℓhA ℓoB ℓhB} (dcA : DCat ℓoA ℓhA) (dcB : DCat ℓoB ℓhB) (cf : dc.cat dcA ++> dc.cat dcB) → Set ?
--isDaggerFunctor dcA dcB cf 

record _dc→_ {α β γ δ} (dcA : DCat α β) (dcB : DCat γ δ) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  no-eta-equality
  constructor mk-df
  field
    f : dc.cat dcA ++> dc.cat dcB
    hom-† : {x y : dc.Obj dcA} → (φ : dc.Hom dcA x y) → f.hom f (dc.† dcA φ) == dc.† dcB (f.hom f φ)
  open _++>_ f public
infix 1 _dc→_
module df = _dc→_

dc-id : ∀{ℓo ℓh} (dc : DCat ℓo ℓh) → (dc dc→ dc)
df.f (dc-id dc) = c-id (dc.cat dc)
df.hom-† (dc-id dc) φ = refl

_dc∘_ : ∀{ℓoA ℓhA ℓoB ℓhB ℓoC ℓhC} {dcA : DCat ℓoA ℓhA} {dcB : DCat ℓoB ℓhB} {dcC : DCat ℓoC ℓhC} →
  (dcB dc→ dcC) → (dcA dc→ dcB) → (dcA dc→ dcC)
df.f (dcg dc∘ dcf) = df.f dcg c∘ df.f dcf
df.hom-† (dcg dc∘ dcf) φ = map= (df.hom dcg) (df.hom-† dcf φ) • df.hom-† dcg (df.hom dcf φ)
infixl 10 _dc∘_

--† is a †-functor!
--dc† : ∀{ℓo ℓh} (dc : DCat ℓo ℓh) 

dfunctorext : ∀{ℓoA}{ℓhA}{ℓoB}{ℓhB} → {dcA : DCat ℓoA ℓhA} → {dcB : DCat ℓoB ℓhB} → {dcf dcg : dcA dc→ dcB}
  → (df.f dcf == df.f dcg) → dcf == dcg
dfunctorext {ℓoA}{ℓhA}{ℓoB}{ℓhB} {dcA}{dcB} {mk-df cf p} {mk-df .cf q} refl = map= (mk-df cf) (λi= x => λi= y => λ= φ => uip)

----adjoints-----------------------------------

cBidir : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Cat ℓo ℓh
c.Obj (cBidir c) = c.Obj c
c.Hom (cBidir c) x y = c.Hom c x y × c.Hom c y x
c.id (cBidir c) x = (Cat.id c x) , (Cat.id c x)
c.comp (cBidir c) ψ φ = (c $ prl ψ m∘ prl φ) , (c $ prr φ m∘ prr ψ)
c.m∘assoc' (cBidir c) = ×ext (c.m∘assoc' c) (sym (c.m∘assoc' c))
c.m∘lunit' (cBidir c) = ×ext (c.m∘lunit' c) (c.m∘runit' c)
c.m∘runit' (cBidir c) = ×ext (c.m∘runit' c) (c.m∘lunit' c)

bidirIsDCat : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → IsDCat (cBidir c)
IsDCat.† (bidirIsDCat c) φ = prr φ , prl φ
IsDCat.†-id (bidirIsDCat c) x = refl
IsDCat.†-m∘ (bidirIsDCat c) ψ φ = refl
IsDCat.††-eq (bidirIsDCat c) φ = refl

dcBidir : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → DCat ℓo ℓh
DCat.cat (dcBidir c) = cBidir c
DCat.isDCat (dcBidir c) = bidirIsDCat c

cZigzags : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → Cat ℓo (ℓo ⊔ ℓh)
Cat.Obj (cZigzags c) = c.Obj c
Cat.Hom (cZigzags c) x y = Zigzag c x y
Cat.id (cZigzags c) x = zz-nil
Cat.comp (cZigzags c) η ζ = ζ zz• η
Cat.m∘assoc' (cZigzags c) {w} {x} {y} {z} {θ} {η} {ζ} = sym (zz•assoc ζ η θ)
Cat.m∘lunit' (cZigzags c) = zz•runit _
Cat.m∘runit' (cZigzags c) = zz•lunit _

zigzagsIsDCat : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → IsDCat (cZigzags c)
IsDCat.† (zigzagsIsDCat c) ζ = zz-inv ζ
IsDCat.†-id (zigzagsIsDCat c) x = refl
IsDCat.†-m∘ (zigzagsIsDCat c) η ζ = zz-inv-zz• ζ η
IsDCat.††-eq (zigzagsIsDCat c) ζ = zz-inv-inv ζ

dcZigzags : ∀{ℓo ℓh} → (c : Cat ℓo ℓh) → DCat ℓo (ℓo ⊔ ℓh)
DCat.cat (dcZigzags c) = cZigzags c
DCat.isDCat (dcZigzags c) = zigzagsIsDCat c
