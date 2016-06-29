open import willow.cat.CwF public
open import willow.basic.TransportLemmas public
open import willow.cat.Isomorphism public
open import willow.cat.NaturalTransformation
open import willow.basic.UIP.HeteroIdentity
import willow.cat.Presheaf

module willow.cat.CwF.Psh.TermFunctor {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open willow.cat.Presheaf ℓtm cW

c-pshtm : (cOp (cOp∫ {cA = cOp cPsh} c-dpsh) ++> cSet (ℓtm ⊔ (ℓhW ⊔ ℓoW)))
f.obj c-pshtm (pA , dpT) = Lim dpT
f.hom c-pshtm {pB , dpT} {pA , dpTf} (pf , dpTf=) = --seems I swapped names dpT and dpTf
  mapLim (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpTf=)) ∘ restrLim (c∫-hom pf)
f.hom-id c-pshtm (pA , dpT) = (f.hom c-pshtm (c.id (cOp (cOp∫ c-dpsh)) (pA , dpT))) == idf ∋ (
    let pf : c.Hom cPsh pA pA
        pf = c.id cPsh pA
        --dpTf= : f.hom c-dpsh (c.id cPsh pA) dpT == dpT
        dpT∘f : c∫ pA ++> cSet ℓtm
        dpT∘f = dpT c∘ c∫-hom pf
        dpTf= : dpT c∘ c∫-hom pf == dpT
        dpTf= = map= (λ f → f dpT) (f.hom-id c-dpsh pA)
        nt-tra-dpTf= : dpT∘f nt→ dpT
        nt-tra-dpTf= = (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpTf=))
    in mapLim nt-tra-dpTf= ∘ restrLim (c∫-hom pf) == idf ∋ (
      λ= l => lim-ext (funext λ{(w , a) →
        via Lim.obj ((mapLim nt-tra-dpTf= ∘ restrLim (c∫-hom pf)) l) (w , a) $ refl •
        via nt.obj nt-tra-dpTf= (w , a) (Lim.obj (restrLim (c∫-hom pf) l) (w , a)) $ refl •
        via nt.obj nt-tra-dpTf= (w , a) (Lim.obj l (f.obj (c∫-hom pf) (w , a))) $ refl •
        via nt.obj nt-tra-dpTf= (w , a) (Lim.obj l (w , a)) $ refl •
        via tra! (map= (λ ch → f.obj ch (w , a)) dpTf=) (Lim.obj l (w , a)) $
          happly (nt-tra-set-lemma {cf = dpT∘f}{dpT} dpTf= (w , a)) (Lim.obj l (w , a)) •
        via tra! refl (Lim.obj l (w , a)) $
          happly (map= tra! ((map= (λ ch → f.obj ch (w , a)) dpTf=) == refl ∋ uip)) (Lim.obj l (w , a)) •
        refl
      })
    )
  )
f.hom-m∘ c-pshtm {pC , dpC} {pB , dpB} {pA , dpA} (pf , dpBf=A) (pg , dpCg=B) =
  let pgf : c.Hom cPsh pA pC
      pgf = cPsh $ pg m∘ pf
      dpB∘f : c∫ pA ++> cSet ℓtm
      dpB∘f = dpB c∘ c∫-hom pf
      dpC∘g : c∫ pB ++> cSet ℓtm
      dpC∘g = dpC c∘ c∫-hom pg
      dpC∘g∘f : c∫ pA ++> cSet ℓtm
      dpC∘g∘f = dpC c∘ c∫-hom (pg nt∘ pf)
      dpCgf=A : dpC∘g∘f == dpA
      dpCgf=A = (prr (c∫ c-dpsh $ pf , dpBf=A m∘ (pg , dpCg=B))) 
      nt-tra-Bf→A : dpB∘f nt→ dpA
      nt-tra-Bf→A = (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpBf=A))
      nt-tra-Cg→B : dpC∘g nt→ dpB
      nt-tra-Cg→B = (≅.fwd (i-tra (cExp (c∫ pB) (cSet ℓtm)) dpCg=B))
      nt-tra-Cgf→A : dpC∘g∘f nt→ dpA
      nt-tra-Cgf→A = (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpCgf=A))
  in  (
        mapLim (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpCgf=A)) ∘ restrLim (c∫-hom pgf)
        ==
        (mapLim (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpBf=A)) ∘ restrLim (c∫-hom pf)) ∘
        (mapLim (≅.fwd (i-tra (cExp (c∫ pB) (cSet ℓtm)) dpCg=B)) ∘ restrLim (c∫-hom pg))
      ) ∋ λ= l => lim-ext (funext λ{(w , a) → (
        let b = nt.obj pf w a
            c = nt.obj pg w b
        in  (
          via Lim.obj ((mapLim (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpCgf=A)) ∘ restrLim (c∫-hom pgf)) l) (w , a)
            $ refl •
          via nt.obj nt-tra-Cgf→A (w , a) (Lim.obj (restrLim (c∫-hom pgf) l) (w , a)) $ refl •
          via nt.obj nt-tra-Cgf→A (w , a) (Lim.obj l (f.obj (c∫-hom pgf) (w , a))) $ refl •
          via nt.obj nt-tra-Cgf→A (w , a) (Lim.obj l (w , c)) $ refl •
          via tra! (map= (λ ch → f.obj ch (w , a)) dpCgf=A) (Lim.obj l (w , c)) $
            happly (nt-tra-set-lemma dpCgf=A (w , a)) (Lim.obj l (w , c)) •
          refl
        ) • sym (
          via Lim.obj (
              ((mapLim (≅.fwd (i-tra (cExp (c∫ pA) (cSet ℓtm)) dpBf=A)) ∘ restrLim (c∫-hom pf)) ∘
               (mapLim (≅.fwd (i-tra (cExp (c∫ pB) (cSet ℓtm)) dpCg=B)) ∘ restrLim (c∫-hom pg)))
            l) (w , a) $ refl •
          via nt.obj nt-tra-Bf→A (w , a) (Lim.obj
              ((mapLim (≅.fwd (i-tra (cExp (c∫ pB) (cSet ℓtm)) dpCg=B)) ∘ restrLim (c∫-hom pg)) l) (w , b)) $ refl •
          via nt.obj nt-tra-Bf→A (w , a) (nt.obj nt-tra-Cg→B (w , b) (Lim.obj l (w , c))) $ refl •
          via tra! (map= (λ ch → f.obj ch (w , a)) dpBf=A) (nt.obj nt-tra-Cg→B (w , b) (Lim.obj l (w , c))) $
            happly (nt-tra-set-lemma dpBf=A (w , a)) (nt.obj nt-tra-Cg→B (w , b) (Lim.obj l (w , c))) •
          via tra! (map= (λ ch → f.obj ch (w , a)) dpBf=A) (tra! (map= (λ ch → f.obj ch (w , b)) dpCg=B) (Lim.obj l (w , c))) $
            map= (tra! (map= (λ ch → f.obj ch (w , a)) dpBf=A))
              (happly (nt-tra-set-lemma dpCg=B (w , b)) (Lim.obj l (w , c))) •
          via tra! (map= (λ ch → f.obj ch (w , b)) dpCg=B • map= (λ ch → f.obj ch (w , a)) dpBf=A) (Lim.obj l (w , c)) $
            happly (tra!-comp
              (map= (λ ch → f.obj ch (w , b)) dpCg=B)
              (map= (λ ch → f.obj ch (w , a)) dpBf=A)
            ) (Lim.obj l (w , c)) •
          happly (map= tra! (
            map= (λ ch → f.obj ch (w , b)) dpCg=B • map= (λ ch → f.obj ch (w , a)) dpBf=A
            ==
            map= (λ ch → f.obj ch (w , a)) dpCgf=A
          ∋ uip)) (Lim.obj l (w , c))
        )
      )})
