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
  {n} {Γ : Con Term n}
  ⦃ ok : No-equality-reflection or-empty Γ ⦄
  where

open import Definition.Untyped.Neutral M type-variant as N
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Reduction R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R

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

  ⇒*U? : Γ ⊢ A → Dec (∃ λ l → Γ ⊢ A ⇒* U l)
  ⇒*U? ⊢A =
    case whNorm ⊢A of λ
      (B , B-whnf , A⇒*B) →
    case is-U B-whnf of λ where
      (yes (l , PE.refl)) → yes (l , A⇒*B)
      (no not) →
        no λ (l , A⇒*U) →
        not (_ , whrDet* (A⇒*U , Uₙ) (A⇒*B , B-whnf))
    where
    is-U : Whnf B → Dec (∃ λ l → U l PE.≡ B)
    is-U Uₙ        = yes (_ , PE.refl)
    is-U Levelₙ    = no λ ()
    is-U zeroᵘₙ    = no λ ()
    is-U sucᵘₙ     = no λ ()
    is-U Liftₙ     = no λ ()
    is-U liftₙ     = no λ ()
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

opaque

  -- It is decidable whether a well-formed type is definitionally equal to an
  -- application of U.

  ≡U? : Γ ⊢ A → Dec (∃ λ l → Γ ⊢ A ≡ U l)
  ≡U? ⊢A =
    Dec-map
      ((λ (_ , A⇒*U) → _ , subset* A⇒*U) , (λ (_ , A≡U) → U-norm A≡U))
      (⇒*U? ⊢A)

private opaque

  -- A lemma used below.

  isLift′ :
    Γ ⊩⟨ l ⟩ A → Dec (∃₂ λ l B → Γ ⊢ A ⇒* Lift l B)
  isLift′ (Levelᵣ A⇒*Level) =
    no λ (_ , _ , A⇒*W) →
    I.Lift≢Level (trans (sym (subset* A⇒*W)) (subset* A⇒*Level))
  isLift′ (Uᵣ′ _ _ _ A⇒*U) =
    no λ (_ , _ , A⇒*) →
    I.U≢Liftⱼ (trans (sym (subset* A⇒*U)) (subset* A⇒*))
  isLift′ (Liftᵣ′ D _ _) =
    yes (_ , _ , D)
  isLift′ (ℕᵣ A⇒*ℕ) =
    no λ (_ , _ , A⇒*W) →
    I.Lift≢ℕ (trans (sym (subset* A⇒*W)) (subset* A⇒*ℕ))
  isLift′ (Emptyᵣ A⇒*Empty) =
    no λ (_ , _ , A⇒*W) →
    Lift≢Emptyⱼ (trans (sym (subset* A⇒*W)) (subset* A⇒*Empty))
  isLift′ (Unitᵣ′ A⇒*Unit _) =
    no λ (_ , _ , A⇒*W) →
    Lift≢Unitⱼ (trans (sym (subset* A⇒*W)) (subset* A⇒*Unit))
  isLift′ (ne′ _ _ A⇒*B B-ne _) =
    no λ (_ , _ , A⇒*W) →
    I.Lift≢ne (ne⁻ B-ne) (trans (sym (subset* A⇒*W)) (subset* A⇒*B))
  isLift′ (Bᵣ′ (BM _ _ _) _ _ A⇒*B _ _ _ _ _) =
    no λ (_ , _ , A⇒*W) →
    Lift≢ΠΣⱼ (trans (sym (subset* A⇒*W)) (subset* A⇒*B))
  isLift′ (Idᵣ ⊩A) =
    no λ (_ , _ , A⇒*Id) →
    I.Id≢Lift $
    trans (sym (subset* (_⊩ₗId_.⇒*Id ⊩A))) (subset* A⇒*Id)

opaque

  -- It is decidable whether a well-formed type reduces to (or does
  -- not reduce to) either a Π-type or a Σ-type.

  isLift : Γ ⊢ A → Dec (∃₂ λ l B → Γ ⊢ A ⇒* Lift l B)
  isLift ⊢A = isLift′ (reducible-⊩ ⊢A .proj₂)

opaque

  ≡Lift? : Γ ⊢ A → Dec (∃₂ λ l B → Γ ⊢ A ≡ Lift l B)
  ≡Lift? ⊢A = Dec-map ((λ (_ , _ , A⇒) → _ , _ , subset* A⇒) , (λ (_ , _ , A≡) → Lift-norm A≡)) (isLift ⊢A)

private opaque

  -- A lemma used below.

  isΠΣ′ :
    Γ ⊩⟨ l ⟩ A → Dec (∃₅ λ b p q B C → Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C)
  isΠΣ′ (Levelᵣ A⇒*Level) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    I.Level≢ΠΣⱼ (trans (sym (subset* A⇒*Level)) (subset* A⇒*W))
  isΠΣ′ (Uᵣ′ _ _ _ A⇒*U) =
    no λ (_ , _ , _ , _ , _ , A⇒*) →
    I.U≢ΠΣⱼ (trans (sym (subset* A⇒*U)) (subset* A⇒*))
  isΠΣ′ (Liftᵣ′ D _ _) =
    no λ (_ , _ , _ , _ , _ , A⇒*) →
    I.Lift≢ΠΣⱼ (trans (sym (subset* D)) (subset* A⇒*))
  isΠΣ′ (ℕᵣ A⇒*ℕ) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    I.ℕ≢ΠΣⱼ (trans (sym (subset* A⇒*ℕ)) (subset* A⇒*W))
  isΠΣ′ (Emptyᵣ A⇒*Empty) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    Empty≢ΠΣⱼ (trans (sym (subset* A⇒*Empty)) (subset* A⇒*W))
  isΠΣ′ (Unitᵣ′ A⇒*Unit _) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    Unit≢ΠΣⱼ (trans (sym (subset* A⇒*Unit)) (subset* A⇒*W))
  isΠΣ′ (ne′ _ _ A⇒*B B-ne _) =
    no λ (_ , _ , _ , _ , _ , A⇒*W) →
    I.ΠΣ≢ne (ne⁻ B-ne) (trans (sym (subset* A⇒*W)) (subset* A⇒*B))
  isΠΣ′ (Πᵣ′ _ _ A⇒*ΠΣ _ _ _ _ _) =
    yes (_ , _ , _ , _ , _ , A⇒*ΠΣ)
  isΠΣ′ (Σᵣ′ _ _ A⇒*ΠΣ _ _ _ _ _) =
    yes (_ , _ , _ , _ , _ , A⇒*ΠΣ)
  isΠΣ′ (Idᵣ ⊩A) =
    no λ (_ , _ , _ , _ , _ , A⇒*Id) →
    I.Id≢ΠΣ $
    trans (sym (subset* (_⊩ₗId_.⇒*Id ⊩A))) (subset* A⇒*Id)

opaque

  -- It is decidable whether a well-formed type reduces to (or does
  -- not reduce to) either a Π-type or a Σ-type.

  isΠΣ : Γ ⊢ A → Dec (∃₅ λ b p q B C → Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C)
  isΠΣ ⊢A = isΠΣ′ (reducible-⊩ ⊢A .proj₂)

opaque

  ≡ΠΣ? : Γ ⊢ A → Dec (∃₅ λ b p q B C → Γ ⊢ A ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C)
  ≡ΠΣ? ⊢A = Dec-map
    ( (λ (_ , _ , _ , _ , _ , A⇒) → _ , _ , _ , _ , _ , subset* A⇒)
    , (λ (_ , _ , _ , _ , _ , A≡) → let _ , _ , A⇒ , _ = ΠΣNorm A≡ in _ , _ , _ , _ , _ , A⇒)
    )
    (isΠΣ ⊢A)

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
    helper (Levelᵣ A⇒*Level) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢Level (trans (sym (subset* A⇒*Id)) (subset* A⇒*Level))
    helper (Uᵣ ⊩U) =
      no λ (_ , _ , _ , A⇒*Id) →
        Id≢U $
        trans (sym (subset* A⇒*Id)) (subset* (_⊩₁U_.⇒*U ⊩U))
    helper (Liftᵣ′ A⇒*Lift _ _) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢Lift (trans (sym (subset* A⇒*Id)) (subset* A⇒*Lift))
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
          (subset* (_⊩Unit⟨_⟩_.⇒*-Unit ⊩Unit))
    helper (ne ⊩A) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢ne (ne⁻ neK) $ trans (sym (subset* A⇒*Id)) (subset* D)
      where
      open _⊩ne_ ⊩A
    helper (Bᵣ (BM _ _ _) ⊩A) =
      no λ (_ , _ , _ , A⇒*Id) →
        I.Id≢ΠΣ $
        trans (sym (subset* A⇒*Id)) (subset* (_⊩ₗB⟨_⟩_.D ⊩A))
    helper (Idᵣ ⊩A) = yes (_ , _ , _ , ⇒*Id)
      where
      open _⊩ₗId_ ⊩A

opaque

  ≡Id? : Γ ⊢ A → Dec (∃₃ λ B t u → Γ ⊢ A ≡ Id B t u)
  ≡Id? ⊢A = Dec-map ((λ (_ , _ , _ , A⇒) → _ , _ , _ , subset* A⇒) , (λ (_ , _ , _ , A≡) → let _ , _ , _ , A⇒ , _ = Id-norm A≡ in _ , _ , _ , A⇒)) (is-Id ⊢A)
