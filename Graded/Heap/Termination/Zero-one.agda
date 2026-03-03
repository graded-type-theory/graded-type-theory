------------------------------------------------------------------------
-- Termination properties of the reduction relation for the Zero-one
-- mode structure. See also Graded.Heap.Termination
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Heap.Assumptions

module Graded.Heap.Termination.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  {mode-variant : Mode-variant 𝕄}
  (open Modality 𝕄)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  (TR : Type-restrictions 𝕄)
  (As : Assumptions UR TR 𝟙)
  where

open Assumptions As
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (sym)
open import Tools.Sum

open import Definition.Untyped M
open import Definition.Untyped.Names-below M
open import Definition.Untyped.Properties M

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Names-below TR
open import Definition.Typed.Well-formed TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage UR
open import Graded.Usage.Properties UR
open import Graded.Restrictions.Zero-one 𝕄 mode-variant

open import Graded.Heap.Untyped type-variant UR factoring-nr 𝟙
open import Graded.Heap.Termination UR TR 𝟙 As
open import Graded.Heap.Typed UR TR factoring-nr 𝟙
open import Graded.Heap.Typed.Inversion UR TR factoring-nr 𝟙
open import Graded.Heap.Typed.Properties UR TR factoring-nr 𝟙
open import Graded.Heap.Typed.Reduction UR TR factoring-nr 𝟙
open import Graded.Heap.Usage type-variant UR factoring-nr 𝟙
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr 𝟙
open import Graded.Heap.Usage.Reduction.Zero-one
  type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available
open import Graded.Heap.Reduction type-variant UR factoring-nr 𝟙

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

  -- The type ⊢▸Final-Reasons is inhabited for closed states under
  -- some assumptions.
  --
  -- Well-typed and well-resourced states that do not reduce have a
  -- value in head position and an empty stack.

  ⊢▸Final-reasons :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M 𝕄) →
    ⊢▸Final-Reasons Δ H t ρ S
  ⊢▸Final-reasons consistent prop ⊢s ▸s f =
    let _ , _ , _ , _ , ∣S∣≡ , _ = ▸ₛ-inv ▸s in
    case ▸Final-reasons′ subtraction-ok prop ▸s f of λ where
      (inj₁ (inj₁ (_ , _  , _ , er∈S , ok))) →
        ⊥-elim (⊢emptyrec∉S (consistent ok) ⊢s er∈S)
      (inj₁ (inj₂ (_ , _ , refl))) →
        let _ , _ , _ , ⊢supᵘ , _ = ⊢ₛ-inv ⊢s in
        ⊥-elim $ Level-not-allowed $
        inversion-Level-⊢ (wf-⊢∷ (inversion-supᵘ ⊢supᵘ .proj₁))
      (inj₂ (inj₁ (_ , _ , refl , v , ¬m))) →
        ⊥-elim (¬m (⊢Matching ∣S∣≡ ⊢s v))
      (inj₂ (inj₂ (inj₁ x))) →
        x
      (inj₂ (inj₂ (inj₂ (_ , refl)))) →
        case ⊢s of λ {
          (⊢ₛ _ ⊢t _) →
        case ⊢∷→Names< ⊢t of λ {
          (defn ()) }}

opaque

  -- A variant of the above

  ⊢▸Final-reasons′ :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M 𝕄) →
    Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩ →
    Value t × S ≡ ε
  ⊢▸Final-reasons′ consistent prop ⊢s ▸s f =
    ⊢▸Final-reasons consistent prop ⊢s ▸s f

------------------------------------------------------------------------
-- Termination properties

opaque

  whBisim :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M 𝕄) →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    ε » Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × wk ρ t [ H ]ₕ ≡ u × Value t
  whBisim consistent prop =
    Termination.whBisim (⊢▸Final-reasons consistent prop)

opaque

  whBisim-initial-ε :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M 𝕄) →
    𝟘ᶜ ▸ t →
    ε » Δ ⊢ t ↘ u ∷ A →
    ∃₅ λ m n H u′ (ρ : Wk m n) → initial t ⇘ ⟨ H , u′ , ρ , ε ⟩ × wk ρ u′ [ H ]ₕ ≡ u × Value u′
  whBisim-initial-ε consistent prop ▸t =
    Termination.whBisim-initial-ε (⊢▸Final-reasons consistent prop)
      (▸-cong (PE.sym ⌞𝟙⌟) ▸t)

opaque

  -- A variant of whBisim-initial-ε without the restriction that the
  -- definition context must be empty.

  whBisim-initial :
    {Γ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » inline-Conᵈ ∇ Γ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M 𝕄) →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸ t →
    glassify ∇ » Γ ⊢ t ↘ u ∷ A →
    ∃₅ λ m n H u′ (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ⇘ ⟨ H , u′ , ρ , ε ⟩ ×
    wk ρ u′ [ H ]ₕ ≡ inlineᵈ ∇ u × Value u′
  whBisim-initial consistent prop ▸∇ ▸t =
    Termination-inline.whBisim-initial
      (⊢▸Final-reasons ⦃ ok = or-empty-inline-Conᵈ ⦄ consistent prop)
      (PE.subst (λ m → ▸[ m ] glassify _) (PE.sym ⌞𝟙⌟) ▸∇) (▸-cong (PE.sym ⌞𝟙⌟) ▸t)

opaque

  ⊢▸-⇘ :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M 𝕄) →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × Value t
  ⊢▸-⇘ consistent prop =
    Termination.⊢▸-⇘ (⊢▸Final-reasons consistent prop)

opaque

  initial-⇘-ε :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M 𝕄) →
    ε » Δ ⊢ t ∷ A → 𝟘ᶜ ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘-ε consistent prop ⊢t ▸t =
    Termination.initial-⇘-ε (⊢▸Final-reasons consistent prop) ⊢t
      (▸-cong (PE.sym ⌞𝟙⌟) ▸t)

opaque

  -- A variant of initial-⇘-ε without the restriction that the
  -- definition context must be empty.

  initial-⇘ :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » inline-Conᵈ ∇ Δ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M 𝕄) →
    ∇ » Δ ⊢ t ∷ A →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘ consistent prop ⊢t ▸∇ ▸t =
    Termination-inline.initial-⇘
      (⊢▸Final-reasons ⦃ ok = or-empty-inline-Conᵈ ⦄ consistent prop)
        ⊢t (PE.subst (λ m → ▸[ m ] glassify _) (PE.sym ⌞𝟙⌟) ▸∇)
        (▸-cong (PE.sym ⌞𝟙⌟) ▸t)
