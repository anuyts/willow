open import willow.cat.Category
open import willow.cat.Opposite
open import willow.cat.Sets
open import willow.cat.Limits
open import willow.cat.OfElements
open import willow.basic.Propositional.HeteroIdentity

module willow.cat.Presheaf {ℓoW ℓhW : Level} (ℓ : Level) (cW : Cat ℓoW ℓhW) where

Psh : Set ((lsuc ℓ) ⊔ ℓhW ⊔ ℓoW)
Psh = cOp cW ++> cSet ℓ

cPsh : Cat (ℓoW ⊔ ℓhW ⊔ lsuc ℓ) (ℓoW ⊔ ℓhW ⊔ lsuc ℓ)
cPsh = cExp (cOp cW) (cSet ℓ)

p⊤ : Psh
p⊤ = cConst (Lift ⊤)

p⊤intro : {pA : Psh} → pA nt→ p⊤
nt.obj p⊤intro w a = lift unit
nt.hom p⊤intro ρ = refl

isterminal-p⊤ : IsTerminal cPsh p⊤
--map void cones from pA to morphisms pA → p⊤
nt.obj (≅.fwd isterminal-p⊤) pA q = lift p⊤intro
nt.hom (≅.fwd isterminal-p⊤) {pA} {pB} pf = λ= q => map= lift (nt-ext refl)
--map morphisms pA → p⊤ to void cones from pA
nt.obj (≅.bck isterminal-p⊤) pA liftp* = mk-cone (λ()) (λ{})
nt.hom (≅.bck isterminal-p⊤) {pA} {pB} pf = λ= liftp* => cone-ext (funext (λ()))
≅.src-id isterminal-p⊤ = nt-ext (λ= pA => λ= q => cone-ext (funext (λ())))
≅.tgt-id isterminal-p⊤ = nt-ext (λ= pA => λ= liftp* => map= lift (nt-ext (λ= w => λ= a => map= lift is¶⊤)))

[isterminal-p⊤] : [IsTerminal] cPsh p⊤
[isterminal-p⊤] = wrap isterminal-p⊤

DPsh : (pA : Psh) → Set ((lsuc ℓ) ⊔ ℓhW ⊔ ℓoW)
DPsh pA = c∫ pA ++> cSet ℓ

c-dpsh : cOp cPsh ++> cSet ((lsuc ℓ) ⊔ ℓhW ⊔ ℓoW)
f.obj c-dpsh pA = DPsh pA
f.hom c-dpsh {pB}{pA} pf dpT = dpT c∘ c∫-hom pf
f.hom-id c-dpsh pA = λ= dpT => functorext (pair-ext refl (λi= w,a => λi= w',a' => λ= ρ,p =>
    map= (f.hom dpT) (pair-ext refl uip)
  ))
f.hom-m∘ c-dpsh {pC}{pB}{pA} pf pg = λ= dpT => functorext (pair-ext refl (λi= w,a => λi= w',a' => λ= ρ,p =>
    map= (f.hom dpT) (pair-ext refl uip)
  ))
  
p∫ : {pA : Psh} (dpT : DPsh pA) → Psh
f.obj (p∫ {pA} dpT) w = Sum λ (a : f.obj pA w) → f.obj dpT (w , a)
f.hom (p∫ {pA} dpT) {v}{w} ρ (a , t) = (f.hom pA ρ a) , (f.hom dpT (ρ , refl) t)
f.hom-id (p∫ {pA} dpT) w = funext λ{(a , t) → pair-hext (happly (f.hom-id pA w) a) (
    via f.hom dpT {w , a} {w , f.hom pA (c.id (cOp cW) w) a} (c.id (cOp cW) w , refl) t $ hrefl h•
    via f.hom dpT {w , a} {w , a} (c.id (c∫ pA) (w , a)) t $
      hhapply
        {B = λ _ → f.obj dpT (w , f.hom pA (c.id (cOp cW) w) a)}
        {B' = λ _ → f.obj dpT (w , a)}
        {f.hom dpT (c.id (cOp cW) w , refl)}
        {f.hom dpT (c.id (c∫ pA) (w , a))}
        ((hdmap= (λ a' → λ p → f.hom dpT {w , a} {w , a'} (c.id (cOp cW) w , p))
            (happly (f.hom-id pA w) a)
          ) =aph=
            huip hrefl
          )
        t h•
    via t $
      hhapply
        {B = λ _ → f.obj dpT (w , a)}
        {B' = λ _ → f.obj dpT (w , a)}
        {f.hom dpT {w , a} {w , a} (c.id (c∫ pA) (w , a))}
        {idf}
        (to-heter (f.hom-id dpT (w , a)))
        t h•
    hrefl
  )}
f.hom-m∘ (p∫ {pA} dpT) {w}{v}{u} ρ σ =
  funext
    {A = ∑ (f.obj pA w) (λ a → f.obj dpT (w , a))}
    {B = λ _ → ∑ (f.obj pA u) (λ a → f.obj dpT (u , a))}
    {f = λ {(a , t) → (f.hom pA (cW $ σ m∘ ρ) a , f.hom dpT (cW $ σ m∘ ρ , refl) t)}}
    {g = λ a,t →
      let a = prl a,t
          t = prr a,t
      in  f.hom pA ρ (f.hom pA σ a) ,
          f.hom dpT (ρ , refl) (f.hom dpT (σ , refl) t)}
    --{g = f.hom (p∫ dpT) ρ ∘ f.hom (p∫ dpT) σ}
    (λ a,t →
      let a = prl a,t
          b = f.hom pA σ a
          c = f.hom pA ρ b
          c' = f.hom pA (cW $ σ m∘ ρ) a
          t = prr a,t
      in  pair-hext
            {A = f.obj pA u}
            {B = λ a₁ → f.obj dpT (u , a₁)}
            {f.hom pA (cW $ σ m∘ ρ) a}{f.hom pA ρ (f.hom pA σ a)} (happly (f.hom-m∘ pA ρ σ) a)
            {f.hom dpT ((cW $ σ m∘ ρ) , refl) t}{f.hom dpT (ρ , refl) (f.hom dpT (σ , refl) t)} (
              via f.hom dpT {w , a}{u , c'} (cW $ σ m∘ ρ , refl) t $ hrefl h•
              via f.hom dpT {w , a}{u , c} (c∫ pA $ (ρ , refl) m∘ (σ , refl)) t $
                hhapply
                  {B = λ _ → f.obj dpT (u , c')}
                  {B' = λ _ → f.obj dpT (u , c)}
                  {f.hom dpT ((cW $ σ m∘ ρ) , refl)}
                  {f.hom dpT (c∫ pA $ (ρ , refl) m∘ (σ , refl))}
                  ((hdmap= (λ c'' → λ p → f.hom dpT {w , a} {u , c''} ((cW $ σ m∘ ρ) , p))
                      (happly (f.hom-m∘ pA ρ σ) a)
                    ) =aph=
                      huip hrefl
                    )
                  t h•
              via (f.hom dpT (ρ , refl) ∘ f.hom dpT (σ , refl)) t $
                to-heter (happly (f.hom-m∘ dpT (ρ , refl) (σ , refl)) t) h•
              hrefl
            )
    )

p-pr : {pA : Psh} {dpT : DPsh pA} → (p∫ dpT nt→ pA)
nt.obj p-pr w = prl
nt.hom p-pr ρ = refl
