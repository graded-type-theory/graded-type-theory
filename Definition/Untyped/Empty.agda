------------------------------------------------------------------------
-- Definitions related to Empty
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Empty
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M

open import Tools.Nat

private variable
  n : Nat

opaque

  -- An eliminator for the empty type which acts as a sink usage wise.

  emptyrec-sink : Term n → Term n → Term n
  emptyrec-sink A t =
    emptyrec 𝟘 (Π 𝟙 , 𝟘 ▷ (Unitˢ 0) ▹ (wk1 A)) t ∘⟨ 𝟙 ⟩ starˢ 0
