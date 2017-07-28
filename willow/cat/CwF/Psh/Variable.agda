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
import willow.cat.Presheaf
import willow.cat.CwF.Psh.TermFunctor
import willow.cat.CwF.Psh.ComprehensionFunctor
open import willow.cat.CwF public

module willow.cat.CwF.Psh.Variable {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓtm cW
open willow.cat.CwF.Psh.TermFunctor ℓtm cW
open willow.cat.CwF.Psh.ComprehensionFunctor ℓtm cW

lim-pshvar-obj : (pA,dpT : Cat.Obj (cOp∫ c-dpsh)) → Lim (f.hom c-dpsh (p-pr {prl pA,dpT}{prr pA,dpT}) (prr pA,dpT))
Lim.obj (lim-pshvar-obj (pA , dpT)) (w , (a , t)) = t
Lim.hom (lim-pshvar-obj (pA , dpT)) {wa , (a , ta)} {wb , (b , tb)} (ρ , p) = to-homog (
    via f.hom dpT {wa , a}{wb , b} (ρ , via b $ map= (λ r → prl r) p • refl) ta $ hrefl h•
    via f.hom dpT {wa , a}{wb , f.hom pA ρ a} (ρ , refl) ta $
      (hdmap= (λ b' → λ q → f.hom dpT {wa , a}{wb , b'} (ρ , q) ta) (map= prl (sym p))) =aph= huip hrefl h•
    via tb $ hdmap= prr p h•
    hrefl
  )

lim-pshvar : Lim (c-pshtm c∘ c-op (cOpDeptPair c-pshcompr (c-dpsh c∘nt nt-op nt-pshwkn)))
Lim.obj lim-pshvar (pA , dpT) = lim-pshvar-obj (pA , dpT)
Lim.hom lim-pshvar {pB , dpB}{pA , dpA} (pf , dpBf=A) = lim-ext (
  let monstrosity : (c∫ (p∫ dpA) ++> cSet ℓtm) $
                      dpB c∘ c∫-hom p-pr c∘ c∫-hom (f.hom c-pshcompr (pf , dpBf=A)) == (dpA c∘ c∫-hom p-pr)
      monstrosity = prr (f.hom (cOpDeptPair c-pshcompr (c-dpsh c∘nt nt-op nt-pshwkn)) (pf , dpBf=A))
  in
  funext
    {f = Lim.obj
           (f.hom
            (c-pshtm c∘
             c-op (cOpDeptPair c-pshcompr (c-dpsh c∘nt nt-op nt-pshwkn)))
            (pf , dpBf=A) (lim-pshvar-obj (pB , dpB)))}
    {g = λ w,a,t → prr (prr w,a,t)}
    (λ{(w , (a , t)) → to-homog (
      via nt.obj (nt-tra monstrosity) (w , a , t) (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t) $ hrefl h•
      via tra! (map= (λ ch → f.obj ch (w , a , t)) monstrosity)
          (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t) $
        to-heter (happly (nt-tra-set-lemma monstrosity (w , a , t))
          (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t)) h•
      via tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t $
        hhapply (htra! (map= (λ ch → f.obj ch (w , a , t)) monstrosity))
          (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) t) h•
      via t $ hhapply (htra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A))) t h•
      hrefl
    )
  }))
