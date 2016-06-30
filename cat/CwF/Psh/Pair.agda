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
import willow.cat.Presheaf
open import willow.cat.CwF public
import willow.cat.CwF.Psh.TermFunctor
import willow.cat.CwF.Psh.ComprehensionFunctor
import willow.cat.CwF.Psh.Variable

module willow.cat.CwF.Psh.Pair {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓtm cW
open willow.cat.CwF.Psh.TermFunctor ℓtm cW
open willow.cat.CwF.Psh.ComprehensionFunctor ℓtm cW
open willow.cat.CwF.Psh.Variable ℓtm cW

p-pshpair : {pΔ pΓ : Psh} → {dpT : DPsh pΓ} → (pf : pΔ nt→ pΓ) → (t : Lim (dpT c∘ c∫-hom pf)) → pΔ nt→ p∫ dpT
nt.obj (p-pshpair {pΔ}{pΓ}{dpT} pf t) w δ =
  let γ : f.obj pΓ w
      γ = nt.obj pf w δ
  in  γ , Lim.obj t (w , δ)
nt.hom (p-pshpair {pΔ}{pΓ}{dpT} pf t) {w}{v} ρ = λ= δ => pair-hext (happly (nt.hom pf ρ) δ) (
    let q : f.hom (f.hom c-dpsh pf dpT) (ρ , refl) (Lim.obj t (w , δ)) == Lim.obj t (v , f.hom pΔ ρ δ)
        q = Lim.hom t (ρ , refl {a = f.hom pΔ ρ δ})
        γ : f.obj pΓ w
        γ = nt.obj pf w δ
    in  via f.hom dpT {w , γ}{v , f.hom pΓ ρ (nt.obj pf w δ)}
            (ρ , refl) (Lim.obj t (w , δ)) $ hrefl h•
        via f.hom dpT {w , γ}{v , nt.obj pf v (f.hom pΔ ρ δ)}
            (ρ , (via nt.obj pf v (f.hom pΔ ρ δ) $ happly (_nt→_.hom pf ρ) δ • refl)) (Lim.obj t (w , δ)) $
          (hdmap= (λ γ' → λ p → f.hom dpT {w , γ}{v , γ'}(ρ , p)(Lim.obj t (w , δ))) (happly (nt.hom pf ρ) δ))
            =aph= huip hrefl h•
        to-heter q
  )

psh-wkn-pair : {pΔ pΓ : Psh} → {dpT : DPsh pΓ} → (pf : pΔ nt→ pΓ) → (t : Lim (dpT c∘ c∫-hom pf)) →
  p-pr nt∘ (p-pshpair pf t) == pf
psh-wkn-pair {pΔ}{pΓ}{dpT} pf t = nt-ext (λ= w => λ= δ => refl)


psh-var-pair : {pΔ pΓ : Psh} → {dpT : DPsh pΓ} → (pf : pΔ nt→ pΓ) → (t : Lim (dpT c∘ c∫-hom pf)) →
  f.hom c-pshtm (p-pshpair pf t , refl) (lim-pshvar-obj (pΓ , dpT)) === t
psh-var-pair {pΔ}{pΓ}{dpT} pf t = h-lim-ext (
    via f.hom c-dpsh (cPsh $ p-pr m∘ p-pshpair pf t) dpT $ happly (sym (f.hom-m∘ c-dpsh (p-pshpair pf t) p-pr)) dpT •
    via f.hom c-dpsh pf dpT $ map= (λ pg → f.hom c-dpsh pg dpT) (psh-wkn-pair pf t) •
    refl
  ) (to-heter (funext λ{(w , δ) → refl}))
