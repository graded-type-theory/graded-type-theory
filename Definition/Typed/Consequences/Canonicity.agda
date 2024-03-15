------------------------------------------------------------------------
-- Canonicity theorems for natural numbers and the empty type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Canonicity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ

private
  variable
    n       : Nat
    A t u v : Term _
    l       : TypeLevel

-- Turns a natural number into its term representation
sucᵏ : Nat → Term n
sucᵏ 0 = zero
sucᵏ (1+ n) = suc (sucᵏ n)

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity″ (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ (ne (neNfₜ neK _ _)) = ⊥-elim (noClosedNe neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity′ (noemb [ℕ]) (ℕₜ n d n≡n prop) =
  let a , b = canonicity″ prop
  in  a , trans (subset*Term (redₜ d)) b
canonicity′ (emb 0<1 [ℕ]) [t] = canonicity′ [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} → ε ⊢ t ∷ ℕ → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity ⊢t with reducibleTerm ⊢t
canonicity ⊢t | [ℕ] , [t] =
  canonicity′ (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

-- Canonicity for Empty

¬Empty′ : ∀ {n} → ε ⊩Empty n ∷Empty → ⊥
¬Empty′ (Emptyₜ _ _ _ (ne (neNfₜ neN _ _))) =
  noClosedNe neN

¬Empty : ∀ {n} → ε ⊢ n ∷ Empty → ⊥
¬Empty {n} ⊢n =
  let [Empty] , [n] = reducibleTerm ⊢n
      [Empty]′ = Emptyᵣ {l = ¹} ([ Emptyⱼ ε , Emptyⱼ ε , id (Emptyⱼ ε) ])
      [n]′ = irrelevanceTerm [Empty] [Empty]′ [n]

  in ¬Empty′ [n]′

opaque

  -- Every closed equality proof reduces to rfl.

  ε⊢⇒*rfl∷Id : ε ⊢ v ∷ Id A t u → ε ⊢ v ⇒* rfl ∷ Id A t u
  ε⊢⇒*rfl∷Id ⊢v =
    case reducibleTerm ⊢v of λ {
      (⊩Id , ⊩v) →
    helper (Id-elim ⊩Id)
      (irrelevanceTerm ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩v) }
    where
    helper :
      (⊩Id : ε ⊩⟨ l ⟩Id Id A t u) →
      ε ⊩⟨ l ⟩ v ∷ Id A t u / Id-intr ⊩Id →
      ε ⊢ v ⇒* rfl ∷ Id A t u
    helper (emb 0<1 ⊩Id) ⊩v                 = helper ⊩Id ⊩v
    helper (noemb ⊩Id)   ⊩v@(_ , v⇒*v′ , _) =
      case ⊩Id∷-view-inhabited ⊩v of λ where
        (ne v′-n _) → ⊥-elim (noClosedNe v′-n)
        (rflᵣ ⊩t≡u) →
          conv* (redₜ v⇒*v′)
            (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩Id))))

opaque

  -- If Id A t u is inhabited in the empty context, then t is
  -- definitionally equal to u at type A.

  ε⊢∷Id→ε⊢≡∷ : ε ⊢ v ∷ Id A t u → ε ⊢ t ≡ u ∷ A
  ε⊢∷Id→ε⊢≡∷ {v} {A} {t} {u} =
    ε ⊢ v ∷ Id A t u         →⟨ ε⊢⇒*rfl∷Id ⟩
    ε ⊢ v ⇒* rfl ∷ Id A t u  →⟨ proj₂ ∘→ proj₂ ∘→ syntacticEqTerm ∘→ subset*Term ⟩
    ε ⊢ rfl ∷ Id A t u       →⟨ inversion-rfl-Id ⟩
    ε ⊢ t ≡ u ∷ A            □
