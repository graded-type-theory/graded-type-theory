------------------------------------------------------------------------
-- Decidability of reducing to Π and Σ-types.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Definition.Typed.Decidable.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant as N
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Reduction R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Properties R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.Relation as Dec

private
  variable
    n   : Nat
    Γ   : Con Term n
    A B : Term n
    l   : Universe-level

opaque

  -- It is decidable whether a well-formed type reduces to an
  -- application of U.

  ⇒*U? : Γ ⊢ A → Dec (∃ λ l → Γ ⊢ A ⇒* U l)
  ⇒*U? ⊢A =
    case whNorm ⊢A of λ
      (B , B-whnf , A⇒*B) →
    case is-U B-whnf of λ where
      (yes (l , PE.refl)) → yes (l , red A⇒*B)
      (no not) →
        no λ (l , A⇒*U) →
        not (_ , whrDet* (A⇒*U , Uₙ) (red A⇒*B , B-whnf))
    where
    is-U : Whnf B → Dec (∃ λ l → U l PE.≡ B)
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

  isB′ : ∀ {l} → Γ ⊩⟨ l ⟩ A → Dec (∃₃ λ W B C → Γ ⊢ A ⇒* ⟦ W ⟧ B ▹ C)
  isB′ (Uᵣ′ _ _ A⇒*U) =
    no λ (_ , _ , _ , A⇒*) →
    I.U≢B _ (trans (sym (subset* (red A⇒*U))) (subset* A⇒*))
  isB′ (ℕᵣ A⇒*ℕ) =
    no λ (_ , _ , _ , A⇒*W) →
    I.ℕ≢B _ (trans (sym (subset* (red A⇒*ℕ))) (subset* A⇒*W))
  isB′ (Emptyᵣ A⇒*Empty) =
    no λ (_ , _ , _ , A⇒*W) →
    Empty≢Bⱼ _ (trans (sym (subset* (red A⇒*Empty))) (subset* A⇒*W))
  isB′ (Unitᵣ (Unitₜ A⇒*Unit _)) =
    no λ (_ , _ , _ , A⇒*W) →
    Unit≢Bⱼ _ (trans (sym (subset* (red A⇒*Unit))) (subset* A⇒*W))
  isB′ (ne′ _ A⇒*B B-ne _) =
    no λ (_ , _ , _ , A⇒*W) →
    I.B≢ne _ B-ne (trans (sym (subset* A⇒*W)) (subset* (red A⇒*B)))
  isB′ (Bᵣ′ _ _ _ A⇒*ΠΣ _ _ _ _ _ _ _) =
    yes (_ , _ , _ , red A⇒*ΠΣ)
  isB′ (Idᵣ ⊩A) =
    no λ (_ , _ , _ , A⇒*Id) →
    I.Id≢⟦⟧▷ $
    trans (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩A)))) (subset* A⇒*Id)
  isB′ (emb ≤ᵘ-refl     ⊩A) = isB′ ⊩A
  isB′ (emb (≤ᵘ-step p) ⊩A) = isB′ (emb p ⊩A)

opaque

  -- It is decidable whether a well-formed type reduces to (or does
  -- not reduce to) either a Π-type or a Σ-type.

  isB : Γ ⊢ A → Dec (∃₃ λ W B C → Γ ⊢ A ⇒* ⟦ W ⟧ B ▹ C)
  isB ⊢A = isB′ (reducible-⊩ ⊢A .proj₂)

opaque

  -- It is decidable whether a well-formed type reduces to (or does
  -- not reduce to) either a Π-type or a Σ-type.

  isΠΣ : Γ ⊢ A → Dec (∃₅ λ b p q B C → Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C)
  isΠΣ ⊢A =
    Dec.map
      (λ { (BM _ _ _ , _ , _ , A⇒*) → _ , _ , _ , _ , _ , A⇒* })
      (λ (_ , _ , _ , _ , _ , A⇒*) → _ , _ , _ , A⇒*)
      (isB ⊢A)

opaque

  -- It is decidable whether a well-formed type reduces to a Π-type.

  isΠ : Γ ⊢ A → Dec (∃₄ λ p q B C → Γ ⊢ A ⇒* Π p , q ▷ B ▹ C)
  isΠ ⊢A with isΠΣ ⊢A
  … | yes (BMΠ , rest)                   = yes rest
  … | yes (BMΣ _ , _ , _ , _ , _ , A⇒*Σ) =
    no λ (_ , _ , _ , _ , A⇒*Π) →
    Π≢Σⱼ (trans (sym (subset* A⇒*Π)) (subset* A⇒*Σ))
  … | no not = no (not ∘→ (_ ,_))

opaque

  -- It is decidable whether a well-formed type reduces to a Σ-type.

  isΣ : Γ ⊢ A → Dec (∃₅ λ s p q B C → Γ ⊢ A ⇒* Σ⟨ s ⟩ p , q ▷ B ▹ C)
  isΣ ⊢A with isΠΣ ⊢A
  … | yes (BMΣ _ , rest)               = yes (_ , rest)
  … | yes (BMΠ , _ , _ , _ , _ , A⇒*Π) =
    no λ (_ , _ , _ , _ , _ , A⇒*Σ) →
    Π≢Σⱼ (trans (sym (subset* A⇒*Π)) (subset* A⇒*Σ))
  … | no not = no (not ∘→ (_ ,_) ∘→ proj₂)

opaque

  -- It is decidable whether a well-formed type reduces to a strong
  -- Σ-type.

  isΣˢ : Γ ⊢ A → Dec (∃₄ λ p q B C → Γ ⊢ A ⇒* Σˢ p , q ▷ B ▹ C)
  isΣˢ ⊢A with isΣ ⊢A
  … | yes (𝕤 , rest)                  = yes rest
  … | yes (𝕨 , _ , _ , _ , _ , A⇒*Σʷ) =
    no λ (_ , _ , _ , _ , A⇒*Σˢ) →
    Σˢ≢Σʷⱼ (trans (sym (subset* A⇒*Σˢ)) (subset* A⇒*Σʷ))
  … | no not = no (not ∘→ (_ ,_))

opaque

  -- It is decidable whether a well-formed type reduces to a weak
  -- Σ-type.

  isΣʷ : Γ ⊢ A → Dec (∃₄ λ p q B C → Γ ⊢ A ⇒* Σʷ p , q ▷ B ▹ C)
  isΣʷ ⊢A with isΣ ⊢A
  … | yes (𝕨 , rest)                  = yes rest
  … | yes (𝕤 , _ , _ , _ , _ , A⇒*Σˢ) =
    no λ (_ , _ , _ , _ , A⇒*Σʷ) →
    Σˢ≢Σʷⱼ (trans (sym (subset* A⇒*Σˢ)) (subset* A⇒*Σʷ))
  … | no not = no (not ∘→ (_ ,_))

opaque

  -- It is decidable whether a well-formed type reduces to an identity
  -- type.

  is-Id : Γ ⊢ A → Dec (∃₃ λ B t u → Γ ⊢ A ⇒* Id B t u)
  is-Id = helper ∘→ proj₂ ∘→ reducible-⊩
    where
    helper : Γ ⊩⟨ l ⟩ A → Dec (∃₃ λ B t u → Γ ⊢ A ⇒* Id B t u)
    helper (Uᵣ ⊩U) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢U $
        trans (sym (subset* A⇒*Id)) (subset* (red (_⊩₁U_.⇒*U ⊩U)))
    helper (ℕᵣ A⇒*ℕ) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢ℕ (trans (sym (subset* A⇒*Id)) (subset* (red A⇒*ℕ)))
    helper (Emptyᵣ A⇒*Empty) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢Empty (trans (sym (subset* A⇒*Id)) (subset* (red A⇒*Empty)))
    helper (Unitᵣ ⊩Unit) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢Unit $
        trans (sym (subset* A⇒*Id))
          (subset* (red (_⊩Unit⟨_⟩_.⇒*-Unit ⊩Unit)))
    helper (ne ⊩A) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢ne neK $ trans (sym (subset* A⇒*Id)) (subset* (red D))
      where
      open _⊩ne_ ⊩A
    helper (Bᵣ _ ⊩A) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢⟦⟧▷ $
        trans (sym (subset* A⇒*Id)) (subset* (red (_⊩ₗB⟨_⟩_.D ⊩A)))
    helper (Idᵣ ⊩A) = yes (_ , _ , _ , red ⇒*Id)
      where
      open _⊩ₗId_ ⊩A
    helper (emb ≤ᵘ-refl     ⊩A) = helper ⊩A
    helper (emb (≤ᵘ-step p) ⊩A) = helper (emb p ⊩A)
