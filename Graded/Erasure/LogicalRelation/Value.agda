------------------------------------------------------------------------
-- Target terms in the logical relation reduce to values
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Tools.PropositionalEquality
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Value
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as

open import Definition.LogicalRelation R
open import Definition.Untyped M

open import Graded.Erasure.LogicalRelation is-𝟘? as
import Graded.Erasure.Target as T
open import Graded.Erasure.Target.Properties

open import Tools.Function
open import Tools.Product as Σ

private variable
  A t : Term _
  u   : T.Term _
  l   : TypeLevel

opaque

  -- If t is related to u, then u reduces to a value.

  reduces-to-value :
    (⊩A : Δ ⊩⟨ l ⟩ A) →
    t ®⟨ l ⟩ u ∷ A / ⊩A →
    ∃ λ v → T.Value v × u T.⇒* v
  reduces-to-value = λ where
    (Uᵣ _)            (Uᵣ v⇒*↯)         → _ , T.↯    , v⇒*↯
    (ℕᵣ _)            (zeroᵣ _ v⇒*zero) → _ , T.zero , v⇒*zero
    (ℕᵣ _)            (sucᵣ _ v⇒*suc _) → _ , T.suc  , v⇒*suc
    (Emptyᵣ _)        ()
    (Unitᵣ _)         (starᵣ _ v⇒*star) → _ , T.star , v⇒*star
    (ne _)            ()
    (Idᵣ _)           (rflᵣ _ v⇒*↯)     → _ , T.↯    , v⇒*↯
    (Bᵣ (BΠ _ _) _)   (u⇒*lam , _)      → _ , T.lam  , u⇒*lam .proj₂
    (emb 0<1 ⊩A)      t®u               → reduces-to-value ⊩A t®u
    (Bᵣ′ (BΣ _ _ _) _ _ _ _ _ _ _ ⊩B _ _)
      (_ , _ , _ , _ , _ , t₂®v₂ , more) →
      Σ-®-elim _ more
        (λ u⇒*v₂ _ →
           Σ.map idᶠ (Σ.map idᶠ (red*concat u⇒*v₂)) $
           reduces-to-value (⊩B _ _ _) t₂®v₂)
        (λ _ u⇒*prod _ _ → _ , T.prod , u⇒*prod)
