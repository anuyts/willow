module willow.cat.Locpath.Inversion where

open import willow.cat.RawZigzag public
open import willow.cat.Locpath.Definition public
open import willow.cat.Locpath.Tools public
open import willow.cat.Locpath.Composition public

--inversion of locpaths----------------------------

eq-lp-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rza rzb : RawZigzag c x y) → (p : EqLocpath c rza rzb) → (EqLocpath c (rz-inv rza) (rz-inv rzb))
eq-lp-inv {_}{_} {c} {x}{y} rz .rz lp-refl = lp-refl
eq-lp-inv {_}{_} {c} {x}{y} .(rzb rz> (c.id c y)) rzb lp-id-fwd =
  tra (λ rz-r' → EqLocpath c (rz-inv (rzb rz> (c.id c y))) rz-r') / (rz•lunit (rz-inv rzb)) of
  eq-lp•rz (rz-refl rz< (c.id c y)) rz-refl (rz-inv rzb) lp-id-bck
eq-lp-inv {_}{_} {c} {x}{y} .(rzb rz< (c.id c y)) rzb lp-id-bck =
  tra (λ rz-r' → EqLocpath c (rz-inv (rzb rz< (c.id c y))) rz-r') / (rz•lunit (rz-inv rzb)) of
  eq-lp•rz (rz-refl rz> (c.id c y)) rz-refl (rz-inv rzb) lp-id-fwd
eq-lp-inv {_}{_} {c} {x}{w} (rz rz> φ rz> ψ) .(rz rz> (c $ ψ m∘ φ)) lp-comp-fwd =
  tra (λ rz-l → EqLocpath c rz-l (rz-inv (rz rz> c $ ψ m∘ φ))) / sym (precomp-twice-bck (rz-inv rz) φ ψ) of
  eq-lp•rz (rz-refl rz< ψ rz< φ) (rz-refl rz< (c $ ψ m∘ φ)) (rz-inv rz) lp-comp-bck
eq-lp-inv {_}{_} {c} {x}{y} (rz rz< φ rz< ψ) .(rz rz< (c $ φ m∘ ψ)) lp-comp-bck = 
  tra (λ rz-l → EqLocpath c rz-l (rz-inv (rz rz< c $ φ m∘ ψ))) / sym (precomp-twice-fwd (rz-inv rz) φ ψ) of
  eq-lp•rz (rz-refl rz> ψ rz> φ) (rz-refl rz> (c $ φ m∘ ψ)) (rz-inv rz) lp-comp-fwd
eq-lp-inv {_}{_} {c} {x}{y} (rz rz> φ rz< .φ) .rz lp-cancel-up = 
  tra (λ rz-l → EqLocpath c rz-l (rz-inv rz)) / sym (precomp-twice-up (rz-inv rz) φ φ) of
  tra (λ rz-r → EqLocpath c (rz-refl rz> φ rz< φ rz• rz-inv rz) rz-r) / rz•lunit (rz-inv rz) of
  eq-lp•rz (rz-refl rz> φ rz< φ) (rz-refl) (rz-inv rz) lp-cancel-up
eq-lp-inv {_}{_} {c} {x}{y} (rz rz< φ rz> .φ) .rz lp-cancel-dn = 
  tra (λ rz-l → EqLocpath c rz-l (rz-inv rz)) / sym (precomp-twice-dn (rz-inv rz) φ φ) of
  tra (λ rz-r → EqLocpath c (rz-refl rz< φ rz> φ rz• rz-inv rz) rz-r) / rz•lunit (rz-inv rz) of
  eq-lp•rz (rz-refl rz< φ rz> φ) (rz-refl) (rz-inv rz) lp-cancel-dn
eq-lp-inv {_}{_} {c} {x}{y} (rza rz> φ) (rzb rz> .φ) (lp-cong-fwd p) =
  rz•eq-lp (rz-refl rz< φ) (rz-inv rza) (rz-inv rzb) (eq-lp-inv rza rzb p)
eq-lp-inv {_}{_} {c} {x}{y} (rza rz< φ) (rzb rz< .φ) (lp-cong-bck p) = 
  rz•eq-lp (rz-refl rz> φ) (rz-inv rza) (rz-inv rzb) (eq-lp-inv rza rzb p)

lp-inv : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (Locpath c x y) → (Locpath c y x)
lp-inv {_}{_}{c}{x} = elim-lp
  (λ y → Locpath c y x)
  (λ y rz → mk-lp (rz-inv rz))
  (λ y rza rzb p → eq-lp (eq-lp-inv rza rzb p))

--composition of inverse locpaths----------------------

pre-lp-tgt-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rz : RawZigzag c x y)
  → (lp-inv (mk-lp rz)) lp• (mk-lp rz) == mk-lp rz-refl
pre-lp-tgt-eq rz-refl = refl
pre-lp-tgt-eq (rz rz> φ) =
       {-
       idee:
       (rz, φ)-1 • (rz, φ)
       = (φ* • rz-1) • (rz • φ)
       = ((φ* • rz-1) • rz) • φ
       = (φ* • (rz-1 • rz)) • φ
       = (φ* • refl) • φ
       := φ* • φ
       = (φ*, φ)
       = refl
       -}
       via (lp-inv (mk-lp (rz rz> φ)) lp• mk-lp (rz rz> φ)) $ refl •
       via mk-lp (rz-inv (rz rz> φ) rz• rz rz> φ) $ refl •
       via mk-lp ((rz-bck φ rz• rz-inv rz) rz• rz rz> φ) $ refl •
       via mk-lp ((rz-bck φ rz• rz-inv rz) rz• (rz rz• (rz-fwd φ))) $
         map= (λ rz' → mk-lp ((rz-bck φ rz• rz-inv rz) rz• rz')) (detach-fwd rz φ) •
       via mk-lp (((rz-bck φ rz• rz-inv rz) rz• rz) rz• (rz-fwd φ)) $
         map= mk-lp (sym (rz•assoc (rz-bck φ rz• rz-inv rz) rz (rz-fwd φ))) •
       via mk-lp (rz-bck φ rz• (rz-inv rz rz• rz) rz• (rz-fwd φ)) $
         map= (λ rz' → mk-lp (rz' rz• (rz-fwd φ))) (rz•assoc (rz-bck φ) (rz-inv rz) rz) •
       via (mk-lp (rz-bck φ) lp• (lp-inv (mk-lp rz) lp• mk-lp rz)) lp• mk-lp (rz-fwd φ) $ refl •
       via (mk-lp (rz-bck φ) lp• mk-lp rz-refl) lp• mk-lp (rz-fwd φ) $
         map= (λ lp' → (mk-lp (rz-bck φ) lp• lp') lp• mk-lp (rz-fwd φ)) (pre-lp-tgt-eq rz) •
       via mk-lp (rz-bck φ rz• rz-fwd φ) $ refl •
       via mk-lp (rz-refl rz< φ rz> φ) $ refl •
       eq-lp lp-cancel-dn
pre-lp-tgt-eq (rz rz< φ) = 
       via (lp-inv (mk-lp (rz rz< φ)) lp• mk-lp (rz rz< φ)) $ refl •
       via mk-lp (rz-inv (rz rz< φ) rz• rz rz< φ) $ refl •
       via mk-lp ((rz-fwd φ rz• rz-inv rz) rz• rz rz< φ) $ refl •
       via mk-lp ((rz-fwd φ rz• rz-inv rz) rz• (rz rz• (rz-bck φ))) $
         map= (λ rz' → mk-lp ((rz-fwd φ rz• rz-inv rz) rz• rz')) (detach-bck rz φ) •
       via mk-lp (((rz-fwd φ rz• rz-inv rz) rz• rz) rz• (rz-bck φ)) $
         map= (mk-lp) (sym (rz•assoc (rz-fwd φ rz• rz-inv rz) rz (rz-bck φ))) •
       via mk-lp (rz-fwd φ rz• (rz-inv rz rz• rz) rz• (rz-bck φ)) $
         map= (λ rz' → mk-lp (rz' rz• (rz-bck φ))) (rz•assoc (rz-fwd φ) (rz-inv rz) rz) •
       via (mk-lp (rz-fwd φ) lp• (lp-inv (mk-lp rz) lp• mk-lp rz)) lp• mk-lp (rz-bck φ) $ refl •
       via (mk-lp (rz-fwd φ) lp• mk-lp rz-refl) lp• mk-lp (rz-bck φ) $
         map= (λ lp' → (mk-lp (rz-fwd φ) lp• lp') lp• mk-lp (rz-bck φ)) (pre-lp-tgt-eq rz) •
       via mk-lp (rz-fwd φ rz• rz-bck φ) $ refl •
       via mk-lp (rz-refl rz> φ rz< φ) $ refl •
       eq-lp lp-cancel-up

lp-tgt-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (lp : Locpath c x y)
  → (lp-inv lp) lp• lp == mk-lp rz-refl
lp-tgt-eq {_}{_} {c} {x} = elimd-lp
  (λ y lp → (lp-inv lp) lp• lp == mk-lp rz-refl)
  (λ y rz → pre-lp-tgt-eq rz)
  (λ y rz rz' p → uip)

pre-lp-src-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (rz : RawZigzag c x y)
  → mk-lp rz lp• lp-inv (mk-lp rz) == mk-lp rz-refl
pre-lp-src-eq rz-refl = refl
pre-lp-src-eq (rz rz> φ) =
  {-
  Idee:
  (r, φ) • (r, φ)-1
  = (r • φ) • (φ* • r-1)
  = ((r • φ) • φ*) • r-1
  = (r • (φ • φ*)) • r-1
  = (r • refl) • r-1
  := r • r-1
  = refl
  -}
  via mk-lp (rz rz> φ) lp• lp-inv (mk-lp (rz rz> φ)) $ refl •
  via mk-lp (rz rz> φ rz• rz-inv (rz rz> φ)) $ refl •
  via mk-lp (rz rz> φ rz• (rz-bck φ rz• rz-inv rz)) $ refl •
  via mk-lp ((rz rz• rz-fwd φ) rz• (rz-bck φ rz• rz-inv rz)) $
    map= (λ rz' → mk-lp (rz' rz• (rz-bck φ rz• rz-inv rz)) ) (detach-fwd rz φ) •
  via mk-lp (((rz rz• rz-fwd φ) rz• rz-bck φ) rz• rz-inv rz) $
    map= mk-lp (sym (rz•assoc (rz rz• rz-fwd φ) (rz-bck φ) (rz-inv rz))) •
  via mk-lp ((rz rz• (rz-fwd φ rz• rz-bck φ)) rz• rz-inv rz) $
    map= (λ rz' → mk-lp (rz' rz• rz-inv rz)) (rz•assoc rz (rz-fwd φ) (rz-bck φ)) •
  via (mk-lp rz lp• mk-lp (rz-fwd φ rz• rz-bck φ)) lp• lp-inv (mk-lp rz) $
    refl •
  via (mk-lp rz lp• mk-lp rz-refl) lp• lp-inv (mk-lp rz) $
    map= (λ lp' → (mk-lp rz lp• lp') lp• lp-inv (mk-lp rz) ) (eq-lp (lp-cancel-up {rz = rz-refl})) •
  via mk-lp (rz rz• rz-inv rz) $ refl •
  pre-lp-src-eq rz
pre-lp-src-eq (rz rz< φ) = 
  via mk-lp (rz rz< φ) lp• lp-inv (mk-lp (rz rz< φ)) $ refl •
  via mk-lp (rz rz< φ rz• rz-inv (rz rz< φ)) $ refl •
  via mk-lp (rz rz< φ rz• (rz-fwd φ rz• rz-inv rz)) $ refl •
  via mk-lp ((rz rz• rz-bck φ) rz• (rz-fwd φ rz• rz-inv rz)) $
    map= (λ rz' → mk-lp (rz' rz• (rz-fwd φ rz• rz-inv rz)) ) (detach-bck rz φ) •
  via mk-lp (((rz rz• rz-bck φ) rz• rz-fwd φ) rz• rz-inv rz) $
    map= mk-lp (sym (rz•assoc (rz rz• rz-bck φ) (rz-fwd φ) (rz-inv rz))) •
  via mk-lp ((rz rz• (rz-bck φ rz• rz-fwd φ)) rz• rz-inv rz) $
    map= (λ rz' → mk-lp (rz' rz• rz-inv rz)) (rz•assoc rz (rz-bck φ) (rz-fwd φ)) •
  via (mk-lp rz lp• mk-lp (rz-bck φ rz• rz-fwd φ)) lp• lp-inv (mk-lp rz) $
    refl •
  via (mk-lp rz lp• mk-lp rz-refl) lp• lp-inv (mk-lp rz) $
    map= (λ lp' → (mk-lp rz lp• lp') lp• lp-inv (mk-lp rz) ) (eq-lp (lp-cancel-dn {rz = rz-refl})) •
  via mk-lp (rz rz• rz-inv rz) $ refl •
  pre-lp-src-eq rz

lp-src-eq : ∀{ℓo ℓh} {c : Cat ℓo ℓh} {x y : c.Obj c} → (lp : Locpath c x y)
  → lp lp• (lp-inv lp) == mk-lp rz-refl
lp-src-eq {_}{_} {c} {x} = elimd-lp
  (λ y lp → lp lp• (lp-inv lp) == mk-lp rz-refl)
  (λ y rz → pre-lp-src-eq rz)
  (λ y rz rz' p → uip)
