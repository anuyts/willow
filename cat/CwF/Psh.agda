
open import willow.basic.TransportLemmas public
open import willow.cat.Isomorphism public
open import willow.cat.NaturalTransformation public
open import willow.basic.UIP.HeteroIdentity public
open import willow.cat.Sets.Limits public
open import willow.cat.OfElements public
open import willow.cat.CwF public
import willow.cat.Presheaf
import willow.cat.CwF.Psh.TermFunctor
import willow.cat.CwF.Psh.ComprehensionFunctor
import willow.cat.CwF.Psh.Variable
import willow.cat.CwF.Psh.Pair

module willow.cat.CwF.Psh {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓtm cW
open willow.cat.CwF.Psh.TermFunctor ℓtm cW
open willow.cat.CwF.Psh.ComprehensionFunctor ℓtm cW
open willow.cat.CwF.Psh.Variable ℓtm cW
open willow.cat.CwF.Psh.Pair ℓtm cW

psh-pair-unpair : {pΔ pΓ : Psh} → {dpT : DPsh pΓ} → (pf : pΔ nt→ (p∫ dpT)) → (p : _) →
      p-pshpair (p-pr nt∘ pf) (tra! p (f.hom c-pshtm (pf , refl) (lim-pshvar-obj (pΓ , dpT)))) == pf
psh-pair-unpair {pΔ}{pΓ}{dpT} pf p = nt-ext (λ= w => λ= δ => pair-hext refl (
    via Lim.obj {cd = dpT c∘ c∫-hom (p-pr nt∘ pf)} (tra! p (f.hom c-pshtm (pf , refl) (lim-pshvar-obj (pΓ , dpT)))) (w , δ) $
      hrefl h•
    via Lim.obj {cd = f.hom c-dpsh pf (f.hom c-dpsh p-pr dpT)} (f.hom c-pshtm (pf , refl) (lim-pshvar-obj (pΓ , dpT))) (w , δ) $
      (hdmap= (λ cd → λ t → Lim.obj {cd = cd} t (w , δ)) (happly (f.hom-m∘ c-dpsh pf p-pr) dpT))
        =aph= hhapply (htra! p) (f.hom c-pshtm (pf , refl) (lim-pshvar-obj (pΓ , dpT))) h•
    hrefl
  ))

cwfPsh : CwF (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (lsuc ℓtm ⊔ (ℓhW ⊔ ℓoW)) (ℓtm ⊔ (ℓhW ⊔ ℓoW))
CwF.cCtx cwfPsh = cPsh
CwF.∙ cwfPsh = p⊤
CwF.∙isterminal cwfPsh = isterminal-p⊤
CwF.c-ty cwfPsh = c-dpsh
CwF.c-tm cwfPsh = c-pshtm
CwF.c-compr cwfPsh = c-pshcompr
CwF.nt-wkn cwfPsh = nt-pshwkn
CwF.lim-var cwfPsh = lim-pshvar
CwF.pair cwfPsh = p-pshpair
CwF.wkn-pair cwfPsh = psh-wkn-pair
CwF.var-pair cwfPsh = psh-var-pair
CwF.pair-unpair cwfPsh {pΔ}{pΓ}{dpT} pf = psh-pair-unpair pf (map= (CwF.Tm cwfPsh pΔ) (sym (CwF.T[][] cwfPsh)))
