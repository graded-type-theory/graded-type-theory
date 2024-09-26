------------------------------------------------------------------------
-- Target terms in the logical relation reduce to values
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Value
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as

open import Definition.LogicalRelation R
open import Definition.Untyped M

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
open import Graded.Erasure.Target as T using (strict)
open import Graded.Erasure.Target.Properties

open import Tools.Function
open import Tools.Product as Σ
open import Tools.PropositionalEquality

private variable
  A t : Term _
  u   : T.Term _
  l   : Universe-level

opaque
  unfolding _®_∷_

  -- In the strict setting, if t is related to u, then u reduces to a
  -- value.

  reduces-to-value :
    str ≡ strict →
    t ® u ∷ A →
    ∃ λ v → T.Value v × u T.⇒* v
  reduces-to-value refl (_ , ⊩A , t®u) = helper ⊩A t®u
    where
    helper :
      (⊩A : Δ ⊩⟨ l ⟩ A) →
      t ®⟨ l ⟩ u ∷ A / ⊩A →
      ∃ λ v → T.Value v × u T.⇒* v
    helper = λ where
      (Uᵣ _)          (Uᵣ v⇒*↯)           → _ , T.↯    , v⇒*↯ refl
      (ℕᵣ _)          (zeroᵣ _ v⇒*zero)   → _ , T.zero , v⇒*zero
      (ℕᵣ _)          (sucᵣ _ v⇒*suc _ _) → _ , T.suc  , v⇒*suc
      (Emptyᵣ _)      ()
      (Unitᵣ _)       (starᵣ _ v⇒*star)   → _ , T.star , v⇒*star
      (ne _)          ()
      (Idᵣ _)         (rflᵣ _ v⇒*↯)       → _ , T.↯    , v⇒*↯ refl
      (Bᵣ (BΠ _ _) _) (u⇒*lam , _)        → _ , T.lam  , u⇒*lam refl
                                                           .proj₂
      (Bᵣ′ (BΣ _ _ _) _ _ _ _ _ _ _ ⊩B _ _)
        (_ , _ , _ , _ , _ , t₂®v₂ , more) →
        Σ-®-elim _ more
          (λ u⇒*v₂ _ →
             Σ.map idᶠ (Σ.map idᶠ (red*concat u⇒*v₂)) $
             helper (⊩B _ _ _) t₂®v₂)
          (λ _ u⇒*prod _ _ → _ , T.prod , u⇒*prod)
      (emb ≤ᵘ-refl     ⊩A) → helper ⊩A
      (emb (≤ᵘ-step p) ⊩A) → helper (emb p ⊩A)

opaque

  -- In the strict setting, if t is related to u at type ℕ, then u
  -- reduces to a numeral.

  reduces-to-numeral :
    str ≡ strict →
    t ® u ∷ℕ →
    ∃ λ v → T.Numeral v × u T.⇒* v
  reduces-to-numeral refl = λ where
    (zeroᵣ _ v⇒*zero)     → _ , T.zero    , v⇒*zero
    (sucᵣ _ v⇒*suc num _) → _ , T.suc num , v⇒*suc
