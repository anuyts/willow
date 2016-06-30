open import willow.basic.TransportLemmas public
open import willow.cat.Isomorphism public
open import willow.cat.NaturalTransformation
open import willow.basic.UIP.HeteroIdentity
open import willow.cat.Opposite public
open import willow.cat.Limits public
open import willow.cat.Isomorphism public
open import willow.cat.OfElements.DeptPairFunctor public
open import willow.cat.Sets.Limits public
open import willow.cat.HomFunctor
open import willow.basic.TransportLemmas
open import willow.basic.UIP.HeteroIdentity
import willow.cat.CwF
import willow.cat.Presheaf

module willow.cat.CwF.Psh.ComprehensionFunctor {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓtm cW
open willow.cat.CwF (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (lsuc ℓtm ⊔ (ℓhW ⊔ ℓoW)) (ℓtm ⊔ (ℓhW ⊔ ℓoW))

c-pshcompr : cOp∫ c-dpsh ++> cPsh
f.obj c-pshcompr (pA , dpT) = p∫ dpT
nt.obj (f.hom c-pshcompr {pA , dpA} {pB , dpB} (pf , dpBf=A)) w (a , ta) =
  (nt.obj pf w a) , (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) ta)
nt.hom (f.hom c-pshcompr {pA , dpA} {pB , dpB} (pf , dpBf=A)) {w}{v} ρ = funext
  {A = f.obj (p∫ dpA) w}
  {B = λ _ → f.obj (p∫ dpB) v}
  {f = λ a,t → (
    let a = prl a,t
        t = prr a,t
    in  f.hom pB ρ (nt.obj pf w a) ,
        f.hom dpB (ρ , refl) (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t)
    )}
  {g = λ a,t → (
    let a = prl a,t
        t = prr a,t
    in  nt.obj pf v (f.hom pA ρ a) ,
        tra! (map= (λ dpX → f.obj dpX (v , f.hom pA ρ a)) (sym dpBf=A)) (f.hom dpA (ρ , refl) t)
  )}
  (λ a,t → 
    let a = prl a,t
        t = prr a,t
    in  pair-hext
          {A = f.obj pB v}{B = λ a₁ → f.obj dpB (v , a₁)}
          {f.hom pB ρ (nt.obj pf w a)}
          {nt.obj pf v (f.hom pA ρ a)}
            (happly (nt.hom pf ρ) a)
          {f.hom dpB (ρ , refl) (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) (prr a,t))}
          {tra! (map= (λ dpX → f.obj dpX (v , f.hom pA ρ a)) (sym dpBf=A)) (f.hom dpA (ρ , refl) t)}
            (
              via f.hom dpB {w , _}{v , f.hom pB ρ (nt.obj pf w a)} (ρ , refl)
                (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t) $
                hrefl h•
              via f.hom dpB {w , _}{v , nt.obj pf v (f.hom pA ρ a)} (ρ , _)
                (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t) $
                (hdmap= (λ b → λ p → f.hom dpB {w , _} {v , b} (ρ , p)
                  (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t)) (happly (nt.hom pf ρ) a)) =aph=
                huip hrefl h•
              via f.hom (dpB c∘ c∫-hom pf) {w , _}{v , f.hom pA ρ a} (ρ , refl)
                (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t) $
                hrefl h•
              via f.hom dpA (ρ , refl) t $
                (hdmap= (λ dpX → f.hom dpX (ρ , refl)) dpBf=A) =aph=
                  hhapply (htra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t h•
              via tra! (map= (λ dpX → f.obj dpX (v , f.hom pA ρ a)) (sym dpBf=A)) (f.hom dpA (ρ , refl) t) $
                hsym (
                  hhapply (htra! (map= (λ dpX → f.obj dpX (v , f.hom pA ρ a)) (sym dpBf=A))) (f.hom dpA (ρ , refl) t)
                ) h•
              hrefl
            )
  )
f.hom-id c-pshcompr (pA , dpT) = nt-ext (λ= w => funext λ{(a , t) → pair-hext refl
    (hhapply (htra! (map= (λ (dpX : c∫ pA ++> cSet ℓtm) → f.obj dpX (w , a))
       (sym
        (map= (λ f → f dpT)
         (funext
          (λ dpT₁ →
             functorext
             (pair-ext refl
              (funexti
               (λ w,a →
                  funexti
                  (λ w',a' →
                     funext (λ ρ,p → map= (f.hom dpT₁) (pair-ext refl uip)))))))))))) t)
  })
f.hom-m∘ c-pshcompr {pA , dpA}{pB , dpB}{pC , dpC} (pg , dpCg=B) (pf , dpBf=A) =
  nt-ext (λ= w => funext
    {A = f.obj (p∫ dpA) w}
    {B = λ _ → f.obj (p∫ dpC) w}
    {f = λ a,t →
      let a = prl a,t
          t = prr a,t
      in  nt.obj (pg nt∘ pf) w a , tra! (map= (λ dpX → f.obj dpX (w , a))
            (sym (prr (cOp∫ c-dpsh $ (pg , dpCg=B) m∘ (pf , dpBf=A))))) t
      }
    {g = λ a,t →
      let a = prl a,t
          b = nt.obj pf w a
          t = prr a,t
      in  nt.obj (pg nt∘ pf) w a ,
            (tra! (map= (λ dpX → f.obj dpX (w , b)) (sym dpCg=B)) ∘ tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t
      }
    (λ{(a , t) → pair-hext refl (
      let b = nt.obj pf w a
      in
      via tra! (map= (λ dpX → f.obj dpX (w , a)) (sym (prr (cOp∫ c-dpsh $ pg , dpCg=B m∘ (pf , dpBf=A))))) t $
        hrefl h•
      via t $
        hhapply (htra! (map= (λ dpX → f.obj dpX (w , a)) (sym (prr (cOp∫ c-dpsh $ pg , dpCg=B m∘ (pf , dpBf=A)))))) t h•
      via (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t $
        hsym (hhapply (htra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t) h•
      via (tra! (map= (λ dpX → f.obj dpX (w , _nt→_.obj pf w a)) (sym dpCg=B))
          ∘ tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t $
        hsym (hhapply (htra! (map= (λ dpX → f.obj dpX (w , _nt→_.obj pf w a)) (sym dpCg=B)))
          ((tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t)
        ) h•
      hrefl
    )})
  )


nt-pshwkn : c-pshcompr nt→ c-co-pr
nt.obj nt-pshwkn (pA , dpT) = p-pr
nt.hom nt-pshwkn {pA , dpA}{pB , dpB} (pf , dpBf=A) = nt-ext refl
