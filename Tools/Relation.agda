------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

module Tools.Relation where

open import Relation.Binary
  using ( Rel
        ; Decidable; Reflexive; Symmetric; Transitive
        ; DecSetoid; Poset; Preorder; Setoid
        ; IsEquivalence; IsPartialOrder; IsPreorder
        )
  public
open import Relation.Nullary using (Dec; yes; no) public
