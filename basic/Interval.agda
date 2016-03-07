module aken.basic.Interval where

open import aken.basic.Basic
open import aken.basic.Function

private
  data I' : Set lzero where
    Zero : I'
    One : I'

I : Set lzero
I = I'

izero : I
izero = Zero

ione : I
ione = One

--ielim : ∀{α} → {}

ielim : ∀{α} → {C : Set α} 
           -> (a b : C)
           -> (p : a == b)
           -> I -> C
ielim a b _ Zero = a
ielim a b _ One = b

postulate 
      seg : izero == ione
      βseg : ∀{α} → {C : Set α} 
           -> (a b : C)
           -> (p : a == b)
           -> (map= (ielim a b p) seg) == p

--http://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/
