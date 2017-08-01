{-# OPTIONS --type-in-type #-}

module willow2.cat.Adjunction.Global where

open import willow2.cat.Category

record _⊣_ {cA cB : Cat} (cl : cA c→ cB) (cr : cB c→ cA) : Set ℓ? where
  field
    η : c-id nt→ cr c∘ cl
    ε : cl c∘ cr nt→ c-id
    .{{ηr∘rε}} : (η nt⊚ nt-id⟨ cr ⟩) nt∘ (nt-id⟨ cr ⟩ nt⊚ ε) ≡ nt-id⟨ (cr c∘ cl) c∘ cr ⟩
    .{{lη∘εl}} : (nt-id⟨ cl ⟩ nt⊚ η) nt∘ (ε nt⊚ nt-id⟨ cl ⟩) ≡ nt-id⟨ (cl c∘ cr) c∘ cl ⟩
