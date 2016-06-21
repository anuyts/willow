open import willow.cat.CwF

module willow.cat.CwF.Psh {ℓoW ℓhW : Level} (ℓty ℓtm : Level) (cW : Cat ℓoW ℓhW) where

open import willow.cat.Presheaf ℓty cW

cwfPsh : CwF {!!} {!!} {!!} {!!}
CwF.cCtx cwfPsh = cPsh
CwF.∙ cwfPsh = p⊤
CwF.∙isterminal cwfPsh = isterminal-p⊤
CwF.c-ty cwfPsh = {!!}
CwF.c-tm cwfPsh = {!!}
CwF.c-compr cwfPsh = {!!}
CwF.nt-wkn cwfPsh = {!!}
CwF.lim-var cwfPsh = {!!}
CwF.canpair cwfPsh = {!!}
