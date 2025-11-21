------------------------------------------------------------------------
-- Termination properties of the reduction relation
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Sum
open import Graded.Heap.Assumptions

module Graded.Heap.Termination
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  (TR : Type-restrictions 𝕄)
  (As : Assumptions UR TR)
  where

open Assumptions As
open Modality 𝕄
open IsMode 𝐌
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (sym)

open import Definition.Untyped M
open import Definition.Untyped.Names-below M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Names-below TR
open import Definition.Typed.Properties TR hiding (_⇨*_)

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage UR
open import Graded.Usage.Properties UR
open import Graded.Restrictions 𝕄 𝐌

open import Graded.Heap.Bisimilarity UR TR
open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Typed.Properties UR TR factoring-nr
open import Graded.Heap.Typed.Reduction UR TR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage.Reduction
  type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr

private variable
  t t′ u A B : Term _
  γ δ η : Conₘ _
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  S S′ : Stack _
  ∇ : DCon (Term 0) _
  Γ Δ : Con Term _
  s s′ : State _ _ _
  m : Mode
  k n : Nat

------------------------------------------------------------------------
-- The type ⊢▸Final-Reasons is inhabited under some assumptions.

opaque

  -- The type ⊢▸Final-Reasons is inhabited for closed states
  --
  -- Well-typed and well-resourced states that do not reduce have a
  -- value in head position and an empty stack.

  ⊢▸Final-reasons-closed :
    {H : Heap 0 n} → ⊢▸Final-Reasons Δ H t ρ S
  ⊢▸Final-reasons-closed {Δ = ε} ⊢s ▸s f =
    case ▸Final-reasons subtraction-ok ▸s f of λ where
      (inj₁ (x , t≡x , d , ∣S∣≡𝟘)) → ⊥-elim $ ¬erased-heap→¬↦● d refl
      (inj₂ (inj₁ (_ , _ , refl , v , ¬m))) →
        ⊥-elim $ ¬m (⊢Matching ⦃ ε ⦄ (▸ₛ-inv ▸s .proj₂ .proj₂ .proj₂ .proj₂ .proj₁) ⊢s v)
      (inj₂ (inj₂ (inj₁ ok))) → ok
      (inj₂ (inj₂ (inj₂ (_ , refl)))) →
        case ⊢s of λ {
          (⊢ₛ _ ⊢t _) →
        case ⊢∷→Names< ⊢t of λ {
          (defn ()) }}

opaque

  -- A variant of the above

  ⊢▸Final-reasons-closed′ :
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩ →
    Value t × S ≡ ε
  ⊢▸Final-reasons-closed′ = ⊢▸Final-reasons-closed

------------------------------------------------------------------------
-- Properties under the assumption that ⊢▸Final-Reasons is inhabited

module Termination {k} {Δ : Con Term k}
  (⊢▸Final-reasons :
    ∀ {m n} {H : Heap k m} {t : Term n}
    {ρ : Wk m n} {S : Stack m} →
    ⊢▸Final-Reasons Δ H t ρ S) where

  opaque

    -- A variant of the property ⊢▸Final-Reasons.

    ⊢▸-⇘-reasons :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      Δ ⊢ₛ s ∷ A →
      ▸ s →
      s ⇘ s′ →
      Value (State.head s′) × State.stack s′ ≡ ε
    ⊢▸-⇘-reasons {s′ = record{}} ⊢s ▸s (d , f) =
      let ⊢s′ = ⊢ₛ-⇾* ⊢s d
          ▸s′ = ▸-⇾* ▸s d
      in  ⊢▸Final-reasons ⊢s′ ▸s′ f

  opaque

    whBisim :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ε » Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
      ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × wk ρ t [ H ]ₕ ≡ u × Value t
    whBisim {s = ⟨ H , t , ρ , S ⟩} ⊢s ▸s d
      with ↘→⇘ As {s = ⟨ H , t , ρ , S ⟩} ⊢s ▸s d
    … |  _ , _ , ⟨ H′ , t′ , ρ′ , S′ ⟩ , d′ , u≡ =
      let v , S≡ε = ⊢▸-⇘-reasons ⊢s ▸s d′
      in  _ , _ , H′ , t′ , ρ′ , lemma S≡ε d′ u≡ v
      where
      lemma :
        S′ ≡ ε → ⟨ H , t , ρ , S ⟩ ⇘ ⟨ H′ , t′ , ρ′ , S′ ⟩ →
        u ≡ ⦅ ⟨ H′ , t′ , ρ′ , S′ ⟩ ⦆ → Value t′ →
        ⟨ H , t , ρ , S ⟩ ⇘ ⟨ H′ , t′ , ρ′ , ε ⟩ × wk ρ′ t′ [ H′ ]ₕ ≡ u × Value t′
      lemma refl d u≡ v = d , PE.sym u≡ , v

  opaque

    whBisim-initial-ε :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      𝟘ᶜ ▸ t →
      ε » Δ ⊢ t ↘ u ∷ A →
      ∃₅ λ m n H u′ (ρ : Wk m n) → initial t ⇘ ⟨ H , u′ , ρ , ε ⟩ × wk ρ u′ [ H ]ₕ ≡ u × Value u′
    whBisim-initial-ε ▸t d =
      let ⊢t = redFirst*Term (d .proj₁) in
      whBisim
        (⊢initial ⊢t) (▸initial ▸t)
        (PE.subst (_ ⊢_↘ _ ∷ _) (PE.sym ⦅initial⦆≡) d)


  opaque

    -- All well-typed and well-resourced states evaluate
    -- to a state with a value in head position and an empty stack

    ⊢▸-⇘ :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × Value t
    ⊢▸-⇘ {s = ⟨ H , t , ρ , S ⟩}  ⊢s ▸s =
      let u , w , d = whNormTerm (⊢⦅⦆ {s = ⟨ H , t , ρ , S ⟩} ⊢s)
          _ , _ , H′ , t′ , ρ′ , d′ , _ , v =
            whBisim ⊢s ▸s (d , w)
      in  _ , _ , H′ , t′ , ρ′ , d′ , v

  opaque

    initial-⇘-ε :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ε » Δ ⊢ t ∷ A → 𝟘ᶜ ▸ t →
      ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
    initial-⇘-ε ⊢t ▸t =
      ⊢▸-⇘ (⊢initial ⊢t) (▸initial ▸t)


module Termination-inline {k} {Δ : Con Term k}
  (⊢▸Final-reasons :
    ∀ {m n} {H : Heap k m} {t : Term n}
    {ρ : Wk m n} {S : Stack m} →
    ⊢▸Final-Reasons (inline-Conᵈ ∇ Δ) H t ρ S) where

  open Termination ⊢▸Final-reasons

  opaque

    -- A variant of whBisim-initial-ε without the restriction that the
    -- definition context must be empty.

    whBisim-initial :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ▸[ 𝟙ᵐ ] glassify ∇ →
      𝟘ᶜ ▸ t →
      glassify ∇ » Δ ⊢ t ↘ u ∷ A →
      ∃₅ λ m n H u′ (ρ : Wk m n) →
      initial (inlineᵈ ∇ t) ⇘ ⟨ H , u′ , ρ , ε ⟩ ×
      wk ρ u′ [ H ]ₕ ≡ inlineᵈ ∇ u × Value u′
    whBisim-initial ▸∇ ▸t t↘u =
      whBisim-initial-ε ⦃ ok = or-empty-inline-Conᵈ ⦄ (▸inlineᵈ ▸∇ ▸t) (⊢inlineᵈ↘inlineᵈ∷ t↘u)

  opaque

    -- A variant of initial-⇘-ε without the restriction that the
    -- definition context must be empty.

    initial-⇘ :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ∇ » Δ ⊢ t ∷ A →
      ▸[ 𝟙ᵐ ] glassify ∇ →
      𝟘ᶜ ▸ t →
      ∃₅ λ m n H u (ρ : Wk m n) →
      initial (inlineᵈ ∇ t) ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
    initial-⇘  ⊢t ▸∇ ▸t =
      initial-⇘-ε ⦃ ok = or-empty-inline-Conᵈ ⦄
        (⊢inlineᵈ∷ ⊢t) (▸inlineᵈ ▸∇ ▸t)

------------------------------------------------------------------------
-- Termination properties for closed states.

opaque

  -- A variant of whBisim for closed states.
  --
  -- All well-typed and well-resourced states that
  -- evaluate to a WHNF "as terms" evaluate to some state with a value
  -- in head position and an empty stack.

  whBisim-closed :
    ε ⊢ₛ s ∷ B → ▸ s → ε » ε ⊢ ⦅ s ⦆ ↘ u ∷ A →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ ×
    wk ρ t [ H ]ₕ ≡ u × Value t
  whBisim-closed =
    Termination.whBisim ⊢▸Final-reasons-closed ⦃ ε ⦄

opaque

  -- A variant of ⊢▸-⇘ for closed states.
  --
  -- All well-typed and well-resourced states evaluate
  -- to a state with a value in head position and an empty stack.

  ⊢▸-⇘-closed :
    ε ⊢ₛ s ∷ B → ▸ s →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × Value t
  ⊢▸-⇘-closed =
    Termination.⊢▸-⇘ ⊢▸Final-reasons-closed ⦃ ε ⦄

opaque

  initial-⇘-closed-ε :
    ε » ε ⊢ t ∷ A → ε ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘-closed-ε =
    Termination.initial-⇘-ε ⊢▸Final-reasons-closed ⦃ ok = ε ⦄


opaque
  unfolding inline-Conᵈ

  -- A variant of initial-⇘-closed-ε without the restriction that the
  -- definition context must be empty.

  initial-⇘-closed :
    ∇ » ε ⊢ t ∷ A → ▸[ 𝟙ᵐ ] glassify ∇ → ε ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘-closed ⊢t ▸∇ ▸t =
    initial-⇘-closed-ε (⊢inlineᵈ∷ ⊢t) (▸inlineᵈ ▸∇ ▸t)
