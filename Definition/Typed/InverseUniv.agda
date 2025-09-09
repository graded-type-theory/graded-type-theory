------------------------------------------------------------------------
-- Every well-formed type is a term in some universe
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.InverseUniv
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Syntactic R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    m n : Nat
    Γ   : Cons m n
    A B : Term n

opaque

  -- Every well-formed type is also a term of type U l for some l.

  inverseUniv : Γ ⊢ A → ∃ λ l → Γ ⊢ A ∷ U l
  inverseUniv (ℕⱼ ⊢Γ)       = _ , ℕⱼ ⊢Γ
  inverseUniv (Emptyⱼ ⊢Γ)   = _ , Emptyⱼ ⊢Γ
  inverseUniv (Unitⱼ ⊢Γ ok) = _ , Unitⱼ ⊢Γ ok
  inverseUniv (Uⱼ ⊢Γ)       = _ , Uⱼ ⊢Γ
  inverseUniv (ΠΣⱼ ⊢B ok)   =
    _ ,
    ΠΣⱼ (inverseUniv (⊢∙→⊢ (wf ⊢B)) .proj₂) (inverseUniv ⊢B .proj₂) ok
  inverseUniv (Idⱼ _ ⊢t ⊢u) =
    _ , Idⱼ (inverseUniv (syntacticTerm ⊢t) .proj₂) ⊢t ⊢u
  inverseUniv (univ ⊢A) = _ , ⊢A

opaque

  -- Being a type is logically equivalent to being a term of type U l
  -- for some l.

  ⊢⇔⊢∷U : Γ ⊢ A ⇔ (∃ λ l → Γ ⊢ A ∷ U l)
  ⊢⇔⊢∷U = inverseUniv , univ ∘→ proj₂

opaque

  -- If A reduces to B, then A reduces to B at type U l for some l.

  inverseUnivRed : Γ ⊢ A ⇒ B → ∃ λ l → Γ ⊢ A ⇒ B ∷ U l
  inverseUnivRed (univ A⇒B) = _ , A⇒B

opaque

  -- Γ ⊢ A ⇒ B is logically equivalent to ∃ λ l → Γ ⊢ A ⇒ B ∷ U l.

  ⊢⇒⇔⊢⇒∷U : Γ ⊢ A ⇒ B ⇔ ∃ λ l → Γ ⊢ A ⇒ B ∷ U l
  ⊢⇒⇔⊢⇒∷U = inverseUnivRed , univ ∘→ proj₂
