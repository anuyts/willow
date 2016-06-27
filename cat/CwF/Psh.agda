open import willow.cat.CwF public
open import willow.basic.TransportLemmas public
open import willow.cat.Isomorphism public
open import willow.cat.NaturalTransformation
open import willow.basic.Propositional.HeteroIdentity

module willow.cat.CwF.Psh {ℓoW ℓhW : Level} (ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open import willow.cat.Presheaf ℓtm cW public

c-pshtm : (cOp (cOp∫ {cA = cOp cPsh} c-dpsh) ++> cSet (ℓtm ⊔ (ℓhW ⊔ ℓoW)))
f.obj c-pshtm (pA , dpT) = Lim dpT
f.hom c-pshtm {pB , dpT} {pA , dpTf} (pf , dpTf=) =
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

c-pshcompr : cOp∫ c-dpsh ++> cPsh
f.obj c-pshcompr (pA , dpT) = psh∫ dpT
nt.obj (f.hom c-pshcompr {pA , dpA} {pB , dpB} (pf , dpBf=A)) w (a , ta) =
  (nt.obj pf w a) , (tra! (map= (λ dpX → f.obj dpX (w , a)) (sym dpBf=A)) ta)
nt.hom (f.hom c-pshcompr {pA , dpA} {pB , dpB} (pf , dpBf=A)) {w}{v} ρ = funext
  {A = f.obj (psh∫ dpA) w}
  {B = λ _ → f.obj (psh∫ dpB) v}
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
                     funext (λ ρ,p → map= (_++>_.hom dpT₁) (pair-ext refl uip)))))))))))) t)
  })
f.hom-m∘ c-pshcompr ψ φ = {!!}

cwfPsh : CwF (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (ℓoW ⊔ ℓhW ⊔ lsuc ℓtm) (lsuc ℓtm ⊔ (ℓhW ⊔ ℓoW)) (ℓtm ⊔ (ℓhW ⊔ ℓoW))
CwF.cCtx cwfPsh = cPsh
CwF.∙ cwfPsh = p⊤
CwF.∙isterminal cwfPsh = isterminal-p⊤
CwF.c-ty cwfPsh = c-dpsh
CwF.c-tm cwfPsh = c-pshtm
CwF.c-compr cwfPsh = c-pshcompr
CwF.nt-wkn cwfPsh = {!!}
CwF.lim-var cwfPsh = {!!}
CwF.canpair cwfPsh = {!!}

