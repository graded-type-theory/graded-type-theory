------------------------------------------------------------------------
-- The natural numbers.
------------------------------------------------------------------------

module Tools.Nat where

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (Nat; _+_; _*_) public
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat.Base using (_⊔_) public
open import Data.Nat.Properties
  using (_≟_;
         +-identityʳ; +-assoc; +-comm;
         *-identityʳ; *-assoc; *-comm; *-zeroʳ;
         ⊔-identityʳ; ⊔-assoc; ⊔-comm; ⊔-idem;
         +-distribˡ-⊔; *-distribˡ-+; *-distribˡ-⊔)
  public
open import Data.Nat.Show using (show) public

pattern 1+ n = suc n
