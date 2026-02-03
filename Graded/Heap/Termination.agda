------------------------------------------------------------------------
-- Termination properties of the reduction relation
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Tools.Sum
open import Graded.Heap.Assumptions

module Graded.Heap.Termination
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (As : Assumptions UR TR)
  where

open Assumptions As
open Modality 𝕄
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
open import Definition.Typed.Inversion TR
open import Definition.Typed.Names-below TR
open import Definition.Typed.Properties TR hiding (_⇨*_)
open import Definition.Typed.Well-formed TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄

open import Graded.Heap.Bisimilarity UR TR
open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Typed.Inversion UR TR factoring-nr
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
  k : Nat

opaque

  -- Well-typed and well-resourced states that do not reduce have a
  -- value in head position and an empty stack.

  ⊢▸Final-reasons :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
    Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩ →
    Value t × S ≡ ε
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

  -- A variant of the property above.

  ⊢▸-⇘-reasons :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
    Δ ⊢ₛ s ∷ A →
    ▸ s →
    s ⇘ s′ →
    Value (State.head s′) × State.stack s′ ≡ ε
  ⊢▸-⇘-reasons {s′ = record{}} consistent prop ⊢s ▸s (d , f) =
    let ⊢s′ = ⊢ₛ-⇾* ⊢s d
        ▸s′ = ▸-⇾* ▸s d
    in  ⊢▸Final-reasons consistent prop ⊢s′ ▸s′ f

opaque

  -- A variant of ⊢▸Final-reasons for closed states
  --
  -- Well-typed and well-resourced states that do not reduce have a
  -- value in head position and an empty stack.

  ⊢▸Final-reasons-closed :
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩ →
    Value t × S ≡ ε
  ⊢▸Final-reasons-closed ⊢s ▸s final =
    ⊢▸Final-reasons ⦃ ε ⦄ (λ _ _ → ¬Empty)
      (λ 0≢0 → ⊥-elim (0≢0 refl)) ⊢s ▸s final

opaque

  ↘→⇘ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    ε » Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
    ∃₃ λ m n (s′ : State _ m n) → s ⇘ s′ × u ≡ ⦅ s′ ⦆
  ↘→⇘ ⊢s ▸s (d , w) =
    let _ , _ , s′ , d₁ , u≡ = ⊢⇒*→⇾* As d ⊢s ▸s
        ▸s′ = ▸-⇾* ▸s d₁
        ⊢s′ = ⊢ₛ-⇾* ⊢s d₁
        _ , s″ , n , d₂ =
          ▸⊢normalize As s′ ▸s′ ⊢s′
        d′ = d₁ ⇨* ⇾ₑ* d₂
        ⊢s″ = ⊢ₛ-⇾* ⊢s d′
        u≡′ = PE.trans u≡ (⇾ₑ*-⦅⦆-≡ d₂)
        w′ = subst (Whnf _) u≡′ w
    in  _ , _ , s″
          , (d′ , λ d″ → whnfRedTerm (⇒ᵥ→⇒ ⊢s″ (Normal-⇾→⇒ᵥ n d″)) w′)
          , u≡′

opaque

  whBisim :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    ε » Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × wk ρ t [ H ]ₕ ≡ u × Value t
  whBisim {s = ⟨ H , t , ρ , S ⟩} consistent prop ⊢s ▸s d
    with ↘→⇘ {s = ⟨ H , t , ρ , S ⟩} ⊢s ▸s d
  … |  _ , _ , ⟨ H′ , t′ , ρ′ , S′ ⟩ , d′ , u≡ =
    let v , S≡ε = ⊢▸-⇘-reasons consistent prop ⊢s ▸s d′
    in  _ , _ , H′ , t′ , ρ′ , lemma S≡ε d′ u≡ v
    where
    lemma :
      S′ ≡ ε → ⟨ H , t , ρ , S ⟩ ⇘ ⟨ H′ , t′ , ρ′ , S′ ⟩ →
      u ≡ ⦅ ⟨ H′ , t′ , ρ′ , S′ ⟩ ⦆ → Value t′ →
      ⟨ H , t , ρ , S ⟩ ⇘ ⟨ H′ , t′ , ρ′ , ε ⟩ × wk ρ′ t′ [ H′ ]ₕ ≡ u × Value t′
    lemma refl d u≡ v = d , PE.sym u≡ , v

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
    whBisim ⦃ ε ⦄ (λ _ _ → ¬Empty)
      (λ 0≢0 → ⊥-elim (0≢0 refl))

opaque

  whBisim-initial-ε :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M semiring-with-meet) →
    𝟘ᶜ ▸ t →
    ε » Δ ⊢ t ↘ u ∷ A →
    ∃₅ λ m n H u′ (ρ : Wk m n) → initial t ⇘ ⟨ H , u′ , ρ , ε ⟩ × wk ρ u′ [ H ]ₕ ≡ u × Value u′
  whBisim-initial-ε consistent prop ▸t d =
    let ⊢t = redFirst*Term (d .proj₁) in
    whBisim consistent prop
      (⊢initial ⊢t) (▸initial ▸t)
      (PE.subst (_ ⊢_↘ _ ∷ _) (PE.sym ⦅initial⦆≡) d)

opaque

  -- A variant of whBisim-initial-ε without the restriction that the
  -- definition context must be empty.

  whBisim-initial :
    {Γ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » inline-Conᵈ ∇ Γ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M semiring-with-meet) →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸ t →
    glassify ∇ » Γ ⊢ t ↘ u ∷ A →
    ∃₅ λ m n H u′ (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ⇘ ⟨ H , u′ , ρ , ε ⟩ ×
    wk ρ u′ [ H ]ₕ ≡ inlineᵈ ∇ u × Value u′
  whBisim-initial {∇} {Γ} consistent nem ▸∇ ▸t t↘u =
    whBisim-initial-ε ⦃ ok = or-empty-inline-Conᵈ ⦄ consistent nem
      (▸inlineᵈ ▸∇ ▸t) (⊢inlineᵈ↘inlineᵈ∷ t↘u)

opaque

  ⊢▸-⇘ :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
    Δ ⊢ₛ s ∷ B →
    ▸ s →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × Value t
  ⊢▸-⇘ {s = ⟨ H , t , ρ , S ⟩} consistent prop ⊢s ▸s =
    let u , w , d = whNormTerm (⊢⦅⦆ {s = ⟨ H , t , ρ , S ⟩} ⊢s)
        _ , _ , H′ , t′ , ρ′ , d′ , _ , v =
          whBisim consistent prop ⊢s ▸s (d , w)
    in  _ , _ , H′ , t′ , ρ′ , d′ , v

opaque

  -- A variant of the above for closed states.
  --
  -- All well-typed and well-resourced states evaluate
  -- to a state with a value in head position and an empty stack.

  ⊢▸-⇘-closed :
    ε ⊢ₛ s ∷ B → ▸ s →
    ∃₅ λ m n H t (ρ : Wk m n) → s ⇘ ⟨ H , t , ρ , ε ⟩ × Value t
  ⊢▸-⇘-closed ⊢s ▸s =
    ⊢▸-⇘ ⦃ ε ⦄ (λ _ _ → ¬Empty)
      (λ 0≢0 → ⊥-elim (0≢0 refl)) ⊢s ▸s

opaque

  initial-⇘-ε :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M semiring-with-meet) →
    ε » Δ ⊢ t ∷ A → 𝟘ᶜ ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘-ε consistent prop ⊢t ▸t =
    ⊢▸-⇘ consistent prop (⊢initial ⊢t) (▸initial ▸t)

opaque

  -- A variant of initial-⇘-ε without the restriction that the
  -- definition context must be empty.

  initial-⇘ :
    {Δ : Con Term k} →
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » inline-Conᵈ ∇ Δ)) →
    (k ≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M semiring-with-meet) →
    ∇ » Δ ⊢ t ∷ A →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘ consistent prop ⊢t ▸∇ ▸t =
    initial-⇘-ε ⦃ ok = or-empty-inline-Conᵈ ⦄ consistent prop
      (⊢inlineᵈ∷ ⊢t) (▸inlineᵈ ▸∇ ▸t)

opaque

  initial-⇘-closed-ε :
    ε » ε ⊢ t ∷ A → ε ▸ t →
    ∃₅ λ m n H u (ρ : Wk m n)→ initial t ⇘ ⟨ H , u , ρ , ε ⟩ × Value u
  initial-⇘-closed-ε ⊢t ▸t =
    initial-⇘-ε ⦃ ok = ε ⦄
      (λ _ _ → ¬Empty) (λ 0≢0 → ⊥-elim (0≢0 refl)) ⊢t ▸t

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
