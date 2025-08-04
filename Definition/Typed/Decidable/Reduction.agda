------------------------------------------------------------------------
-- Decidability of whether terms reduce to applications of specific
-- type formers (in the absence of equality reflection, or for empty
-- contexts)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Definition.Typed.Decidable.Reduction
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  {m} {∇ : DCon (Term 0) m}
  {n} {Γ : Con Term n}
  ⦃ ok : No-equality-reflection or-empty Γ ⦄
  where

open import Definition.Untyped.Neutral M type-variant as N
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Reduction R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Properties R

open import Tools.Function
open import Tools.Product
import Tools.Relation as Dec

private
  variable
    A B : Term n
    l   : Universe-level

opaque

  -- It is decidable whether a well-formed type reduces to an
  -- application of U.

  ⇒*U? : ∇ » Γ ⊢ A → Dec (∃ λ l → ∇ » Γ ⊢ A ⇒* U l)
  ⇒*U? ⊢A =
    case whNorm ⊢A of λ
      (B , B-whnf , A⇒*B) →
    case is-U B-whnf of λ where
      (yes (l , PE.refl)) → yes (l , A⇒*B)
      (no not) →
        no λ (l , A⇒*U) →
        not (_ , whrDet* (A⇒*U , Uₙ) (A⇒*B , B-whnf))
    where
    is-U : Whnf ∇ B → Dec (∃ λ l → U l PE.≡ B)
    is-U Uₙ        = yes (_ , PE.refl)
    is-U ΠΣₙ       = no λ ()
    is-U ℕₙ        = no λ ()
    is-U Unitₙ     = no λ ()
    is-U Emptyₙ    = no λ ()
    is-U Idₙ       = no λ ()
    is-U lamₙ      = no λ ()
    is-U zeroₙ     = no λ ()
    is-U sucₙ      = no λ ()
    is-U starₙ     = no λ ()
    is-U prodₙ     = no λ ()
    is-U rflₙ      = no λ ()
    is-U (ne B-ne) = no (N.U≢ne B-ne ∘→ proj₂)

private opaque

  -- A lemma used below.

  isΠΣ′ :
    ∇ » Γ ⊩⟨ l ⟩ A → Dec (∃₅ λ b p q B C → ∇ » Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C)
  isΠΣ′ (Uᵣ′ _ _ A⇒*U) =
    no λ (_ , _ , _ , _ , _ , A⇒*) →
    I.U≢ΠΣⱼ (trans (sym (subset* A⇒*U)) (subset* A⇒*))
  isΠΣ′ (ℕᵣ A⇒*ℕ) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    I.ℕ≢ΠΣⱼ (trans (sym (subset* A⇒*ℕ)) (subset* A⇒*W))
  isΠΣ′ (Emptyᵣ A⇒*Empty) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    Empty≢ΠΣⱼ (trans (sym (subset* A⇒*Empty)) (subset* A⇒*W))
  isΠΣ′ (Unitᵣ (Unitₜ A⇒*Unit _)) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    Unit≢ΠΣⱼ (trans (sym (subset* A⇒*Unit)) (subset* A⇒*W))
  isΠΣ′ (ne′ _ A⇒*B B-ne _) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    I.ΠΣ≢ne B-ne (trans (sym (subset* A⇒*W)) (subset* A⇒*B))
  isΠΣ′ (Πᵣ′ _ _ A⇒*ΠΣ _ _ _ _ _) =
    yes (_ , _ , _ , _ , _ , A⇒*ΠΣ)
  isΠΣ′ (Σᵣ′ _ _ A⇒*ΠΣ _ _ _ _ _) =
    yes (_ , _ , _ , _ , _ , A⇒*ΠΣ)
  isΠΣ′ (Idᵣ ⊩A) =
    no λ (_ , _ , _ , _ , _ , A⇒*Id) →
    I.Id≢ΠΣ $
    trans (sym (subset* (_⊩ₗId_.⇒*Id ⊩A))) (subset* A⇒*Id)
  isΠΣ′ (emb ≤ᵘ-refl     ⊩A) = isΠΣ′ ⊩A
  isΠΣ′ (emb (≤ᵘ-step p) ⊩A) = isΠΣ′ (emb p ⊩A)

opaque

  -- It is decidable whether a well-formed type reduces to (or does
  -- not reduce to) either a Π-type or a Σ-type.

  isΠΣ : ∇ » Γ ⊢ A → Dec (∃₅ λ b p q B C → ∇ » Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C)
  isΠΣ ⊢A = isΠΣ′ (reducible-⊩ ⊢A .proj₂)

opaque

  -- It is decidable whether a well-formed type reduces to a Π-type.

  isΠ : ∇ » Γ ⊢ A → Dec (∃₄ λ p q B C → ∇ » Γ ⊢ A ⇒* Π p , q ▷ B ▹ C)
  isΠ ⊢A with isΠΣ ⊢A
  … | yes (BMΠ , rest)                   = yes rest
  … | yes (BMΣ _ , _ , _ , _ , _ , A⇒*Σ) =
    no λ (_ , _ , _ , _ , A⇒*Π) →
    Π≢Σⱼ (trans (sym (subset* A⇒*Π)) (subset* A⇒*Σ))
  … | no not = no (not ∘→ (_ ,_))

opaque

  -- It is decidable whether a well-formed type reduces to a Σ-type.

  isΣ : ∇ » Γ ⊢ A → Dec (∃₅ λ s p q B C → ∇ » Γ ⊢ A ⇒* Σ⟨ s ⟩ p , q ▷ B ▹ C)
  isΣ ⊢A with isΠΣ ⊢A
  … | yes (BMΣ _ , rest)               = yes (_ , rest)
  … | yes (BMΠ , _ , _ , _ , _ , A⇒*Π) =
    no λ (_ , _ , _ , _ , _ , A⇒*Σ) →
    Π≢Σⱼ (trans (sym (subset* A⇒*Π)) (subset* A⇒*Σ))
  … | no not = no (not ∘→ (_ ,_) ∘→ proj₂)

opaque

  -- It is decidable whether a well-formed type reduces to a strong
  -- Σ-type.

  isΣˢ : ∇ » Γ ⊢ A → Dec (∃₄ λ p q B C → ∇ » Γ ⊢ A ⇒* Σˢ p , q ▷ B ▹ C)
  isΣˢ ⊢A with isΣ ⊢A
  … | yes (𝕤 , rest)                  = yes rest
  … | yes (𝕨 , _ , _ , _ , _ , A⇒*Σʷ) =
    no λ (_ , _ , _ , _ , A⇒*Σˢ) →
    Σˢ≢Σʷⱼ (trans (sym (subset* A⇒*Σˢ)) (subset* A⇒*Σʷ))
  … | no not = no (not ∘→ (_ ,_))

opaque

  -- It is decidable whether a well-formed type reduces to a weak
  -- Σ-type.

  isΣʷ : ∇ » Γ ⊢ A → Dec (∃₄ λ p q B C → ∇ » Γ ⊢ A ⇒* Σʷ p , q ▷ B ▹ C)
  isΣʷ ⊢A with isΣ ⊢A
  … | yes (𝕨 , rest)                  = yes rest
  … | yes (𝕤 , _ , _ , _ , _ , A⇒*Σˢ) =
    no λ (_ , _ , _ , _ , A⇒*Σʷ) →
    Σˢ≢Σʷⱼ (trans (sym (subset* A⇒*Σˢ)) (subset* A⇒*Σʷ))
  … | no not = no (not ∘→ (_ ,_))

opaque

  -- It is decidable whether a well-formed type reduces to an identity
  -- type.

  is-Id : ∇ » Γ ⊢ A → Dec (∃₃ λ B t u → ∇ » Γ ⊢ A ⇒* Id B t u)
  is-Id = helper ∘→ proj₂ ∘→ reducible-⊩
    where
    helper : ∇ » Γ ⊩⟨ l ⟩ A → Dec (∃₃ λ B t u → ∇ » Γ ⊢ A ⇒* Id B t u)
    helper (Uᵣ ⊩U) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢U $
        trans (sym (subset* A⇒*Id)) (subset* (_⊩₁U_.⇒*U ⊩U))
    helper (ℕᵣ A⇒*ℕ) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢ℕ (trans (sym (subset* A⇒*Id)) (subset* A⇒*ℕ))
    helper (Emptyᵣ A⇒*Empty) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢Empty (trans (sym (subset* A⇒*Id)) (subset* A⇒*Empty))
    helper (Unitᵣ ⊩Unit) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢Unit $
        trans (sym (subset* A⇒*Id))
          (subset* (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩Unit))
    helper (ne ⊩A) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢ne neK $ trans (sym (subset* A⇒*Id)) (subset* D)
      where
      open _⊩ne_ ⊩A
    helper (Bᵣ (BM _ _ _) ⊩A) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢ΠΣ $
        trans (sym (subset* A⇒*Id)) (subset* (_⊩ₗB⟨_⟩_.D ⊩A))
    helper (Idᵣ ⊩A) = yes (_ , _ , _ , ⇒*Id)
      where
      open _⊩ₗId_ ⊩A
    helper (emb ≤ᵘ-refl     ⊩A) = helper ⊩A
    helper (emb (≤ᵘ-step p) ⊩A) = helper (emb p ⊩A)
