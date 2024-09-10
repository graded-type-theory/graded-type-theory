------------------------------------------------------------------------
-- Every well-formed type is a term in some universe
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.InverseUniv
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Consequences.Syntactic R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A : Term n

opaque

  -- Every well-formed type is also a term of type U l for some l.

  inverseUniv : Γ ⊢ A → ∃ λ l → Γ ⊢ A ∷ U l
  inverseUniv (ℕⱼ ⊢Γ)        = _ , ℕⱼ ⊢Γ
  inverseUniv (Emptyⱼ ⊢Γ)    = _ , Emptyⱼ ⊢Γ
  inverseUniv (Unitⱼ ⊢Γ ok)  = _ , Unitⱼ ⊢Γ ok
  inverseUniv (Uⱼ ⊢Γ)        = _ , Uⱼ ⊢Γ
  inverseUniv (ΠΣⱼ ⊢A ⊢B ok) =
    _ , ΠΣⱼ (inverseUniv ⊢A .proj₂) (inverseUniv ⊢B .proj₂) ok
  inverseUniv (Idⱼ ⊢t ⊢u) =
    _ , Idⱼ (inverseUniv (syntacticTerm ⊢t) .proj₂) ⊢t ⊢u
  inverseUniv (univ ⊢A) = _ , ⊢A

opaque

  -- Being a type is logically equivalent to being a term of type U l
  -- for some l.

  ⊢⇔⊢∷U : Γ ⊢ A ⇔ (∃ λ l → Γ ⊢ A ∷ U l)
  ⊢⇔⊢∷U = inverseUniv , univ ∘→ proj₂
