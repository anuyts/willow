open import willow.cat.CwF public
open import willow.basic.TransportLemmas public
open import willow.cat.Isomorphism public
open import willow.cat.NaturalTransformation
open import willow.basic.Propositional.HeteroIdentity
import willow.cat.Presheaf
import willow.cat.CwF.Psh.TermFunctor
import willow.cat.CwF.Psh.ComprehensionFunctor
import willow.cat.CwF.Psh.Variable

module willow.cat.CwF.Psh {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓtm cW
open willow.cat.CwF.Psh.TermFunctor ℓtm cW
open willow.cat.CwF.Psh.ComprehensionFunctor ℓtm cW
open willow.cat.CwF.Psh.Variable ℓtm cW

--pshcanpair : {pB pA : Psh} {dpT : DPsh pA} → IsIso (cSet ((lsuc ℓtm) ⊔ ℓoW ⊔ ℓhW))

cwfPsh : CwF (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (lsuc ℓtm ⊔ (ℓhW ⊔ ℓoW)) (ℓtm ⊔ (ℓhW ⊔ ℓoW))
CwF.cCtx cwfPsh = cPsh
CwF.∙ cwfPsh = p⊤
CwF.∙isterminal cwfPsh = isterminal-p⊤
CwF.c-ty cwfPsh = c-dpsh
CwF.c-tm cwfPsh = c-pshtm
CwF.c-compr cwfPsh = c-pshcompr
CwF.nt-wkn cwfPsh = nt-pshwkn
CwF.lim-var cwfPsh = lim-pshvar
≅.fwd (prl (CwF.canpair cwfPsh {pB}{pA}{dpT})) = _
nt.obj (lower (Iso.bck (prl (CwF.canpair cwfPsh {pB}{pA}{dpT})) (pf , t))) w b = nt.obj pf w b , Lim.obj t (w , b)
nt.hom (lower (Iso.bck (prl (CwF.canpair cwfPsh {pB}{pA}{dpT})) (pf , t))) {w}{v} ρ = λ= b =>
  pair-hext (happly (nt.hom pf ρ) b) (
    let q : f.hom (f.hom c-dpsh pf dpT) (ρ , refl) (Lim.obj t (w , b)) == Lim.obj t (v , f.hom pB ρ b)
        q = Lim.hom t (ρ , refl {a = f.hom pB ρ b})
    in  via f.hom dpT (ρ , (via nt.obj pf v (f.hom pB ρ b) $ happly (_nt→_.hom pf ρ) b • refl)) (Lim.obj t (w , b)) $
          {!!} h•
        to-heter q
  )
≅.src-id (prl (CwF.canpair cwfPsh {pB}{pA}{dpT})) = {!!}
≅.tgt-id (prl (CwF.canpair cwfPsh {pB}{pA}{dpT})) = {!!}
prr (CwF.canpair cwfPsh {pB}{pA}{dpT}) = refl

