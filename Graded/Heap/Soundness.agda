------------------------------------------------------------------------
-- Resource correctness of the heap semantics.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Heap.Assumptions
open import Definition.Typed.Restrictions
open import Tools.Sum

module Graded.Heap.Soundness
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
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.Reasoning.PartialOrder as RPo

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR
open import Definition.LogicalRelation.Unary TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage.Reduction
  type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available
open import Graded.Heap.Termination UR TR As
open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Typed.Inversion UR TR factoring-nr
open import Graded.Heap.Typed.Reduction UR TR factoring-nr
open import Graded.Heap.Typed.Properties UR TR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr

private variable
  k : Nat
  n t A : Term _
  s : State _ _ _
  γ δ η : Conₘ _
  ∇ : DCon (Term 0) _
  Γ Δ : Con Term _
  H : Heap _ _
  ρ : Wk _ _
  S : Stack _
  m : Mode
  x : Fin _
  p : M

opaque

  -- Heap lookups always succeed for well-resourced and well-typed
  -- states (given some assumptions)

  lookup-succeeds :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k PE.≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
    ∣ S ∣≡ p →
    ▸ ⟨ H , var x , ρ , S ⟩ → Δ ⊢ₛ ⟨ H , var x , ρ , S ⟩ ∷ A →
    ∃₃ λ n H′ (c′ : Entry _ n) → H ⊢ wkVar ρ x ↦[ p ] c′ ⨾ H′
  lookup-succeeds {k = 0} _ _ ∣S∣≡ ▸s _ =
    ▸↦[]-closed subtraction-ok ∣S∣≡ ▸s
  lookup-succeeds {k = 1+ _} {H} {x} {ρ} consistent prop ∣S∣≡ ▸s ⊢s =
    let _ , _ , _ , _ , _ , _ , _ , ▸S , _ = ▸ₛ-inv ▸s in
    case ↦⊎↦● {H = H} (wkVar ρ x) of λ where
      (inj₁ (_ , _ , d)) →
        let H′ , d = ▸↦→↦[] subtraction-ok ∣S∣≡ d ▸s
        in  _ , _ , _ , d
      (inj₂ d) →
        let nem , 𝟘-wb = prop λ ()
        in  case ▸∣∣≢𝟘 nem ⦃ 𝟘-wb ⦄ ▸S of λ where
          (inj₁ ∣S∣≢𝟘) → ⊥-elim (∣S∣≢𝟘 (▸s● subtraction-ok ⦃ 𝟘-wb ⦄ d ▸s))
          (inj₂ (er∈ , ok)) →
            ⊥-elim (⊢emptyrec∉S (consistent ok) ⊢s er∈)

opaque

  -- Heap lookups always succeed for well-resourced and well-typed
  -- states (given some assumptions)

  lookup-succeeds′ :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Consistent (ε » Δ) →
    No-erased-matches′ type-variant UR →
    Has-well-behaved-zero M semiring-with-meet →
    ∣ S ∣≡ p →
    ▸ ⟨ H , var x , ρ , S ⟩ → Δ ⊢ₛ ⟨ H , var x , ρ , S ⟩ ∷ A →
    ∃₃ λ n H′ (c′ : Entry _ n) → H ⊢ wkVar ρ x ↦[ p ] c′ ⨾ H′
  lookup-succeeds′ consistent nem 𝟘-wb =
    lookup-succeeds (λ _ → consistent) (λ _ → nem , 𝟘-wb)

opaque

  -- A lemma used to prove redNumeral.

  redNumeral′ : {Δ : Con Term k}
                ⦃ ok : No-equality-reflection or-empty Δ ⦄
             → (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ))
             → (k PE.≢ 0 →
                No-erased-matches′ type-variant UR ×
                Has-well-behaved-zero M semiring-with-meet)
             → ε » Δ ⊩ℕ n ∷ℕ → n PE.≡ ⦅ s ⦆ → Δ ⊢ₛ s ∷ ℕ → ▸ s
             → ∃₅ λ m n H (ρ : Wk m n) t → s ↠* ⟨ H , t , ρ , ε ⟩ ×
               Numeral t × ε » Δ ⊢ ⦅ s ⦆ ≡ wk ρ t [ H ]ₕ ∷ ℕ ×
               ▸ ⟨ H , t , ρ , ε ⟩
  redNumeral′ consistent prop (ℕₜ _ d n≡n (sucᵣ x)) PE.refl ⊢s ▸s =
    case whBisim consistent prop ⊢s ▸s (d , sucₙ) of λ
      (_ , _ , H , t , ρ , (d′ , _) , ≡u , v) →
    case subst-suc {t = wk ρ t} ≡u of λ {
      (inj₁ (x , ≡x)) →
    case wk-var ≡x of λ {
      (_ , PE.refl , _) →
    case v of λ ()};
      (inj₂ (n′ , ≡suc , ≡n)) →
    case wk-suc ≡suc of λ {
      (n″ , PE.refl , ≡n′) →
    case ⇾*→≡ ⊢s d′ of λ
      s≡ →
    case isNumeral? n″ of λ {
      (yes num) →
    _ , _ , _ , _ , _ , ⇾*→↠* d′ , sucₙ num , s≡ , ▸-⇾* ▸s d′ ;
      (no ¬num) →
    case ⊢ₛ-inv (⊢ₛ-⇾* ⊢s d′) of λ
      (_ , _ , ⊢H , ⊢t , ⊢S) →
    case inversion-suc ⊢t of λ
      (⊢n″ , ≡ℕ) →
    case ▸ₛ-inv (▸-⇾* ▸s d′) of λ
      (_ , _ , _ , _ , ∣ε∣≡ , ▸H , ▸t , ▸ε , γ≤) →
    case inv-usage-suc ▸t of λ
      (invUsageSuc ▸n″ δ≤)  →
    case redNumeral′ {s = ⟨ H , n″ , ρ , ε ⟩} consistent prop x
          (PE.sym (PE.trans (PE.cong (_[ H ]ₕ) ≡n′) ≡n))
          (⊢ₛ ⊢H ⊢n″ ε)
          (▸ₛ ∣ε∣≡ ▸H ▸n″ ▸ε (≤ᶜ-trans γ≤ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤))))) of λ
      (_ , _ , H′ , ρ′ , t′ , d₀ , n , s′≡ , ▸s′) →
    case ▸ₛ-inv ▸s′ of λ
      (_ , _ , _ , _ , ∣ε∣≡ , ▸H , ▸t , ▸S , γ≤) →
    _ , _ , _ , _ , _
      , ↠*-concat (⇾*→↠* d′)
          (⇒ₙ sucₕ ¬num ⇨ ↠*-concat (++sucₛ-↠* d₀) (⇒ₙ (numₕ n) ⇨ id))
      , sucₙ n , trans s≡ (suc-cong s′≡)
      , ▸ₛ ∣ε∣≡ ▸H (sucₘ ▸t) ▸S γ≤ }}}

  redNumeral′ consistent prop (ℕₜ _ d n≡n zeroᵣ) PE.refl ⊢s ▸s =
    case whBisim consistent prop ⊢s ▸s (d , zeroₙ) of λ
      (_ , _ , H , t , ρ , (d′ , _) , ≡u , v) →
    case subst-zero {t = wk ρ t} ≡u of λ {
      (inj₁ (x , ≡x)) →
    case wk-var ≡x of λ {
      (_ , PE.refl , w) →
    case v of λ ()} ;
      (inj₂ ≡zero) →
    case wk-zero ≡zero of λ {
      PE.refl →
    _ , _ , _ , _ , _ , ⇾*→↠* d′ , zeroₙ , ⇾*→≡ ⊢s d′ , ▸-⇾* ▸s d′ }}

  redNumeral′
    consistent prop (ℕₜ _ d _ (ne (neNfₜ neK _))) PE.refl ⊢s ▸s =
    let neK = ne→ _ (ne⁻ neK) in
    case whBisim consistent prop ⊢s ▸s (d , ne neK) of λ {
      (_ , _ , H , t , ρ , d′ , PE.refl , v) →
    ⊥-elim $
    Value→¬Neutral (substValue (toSubstₕ H) (wkValue ρ v)) neK }

opaque

  -- If the definition context is empty, then a well-resourced state
  -- of type ℕ reduces to a numeral (given certain assumptions).

  redNumeral : {Δ : Con Term k}
               ⦃ ok : No-equality-reflection or-empty Δ ⦄
             → (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ))
             → (k PE.≢ 0 →
                No-erased-matches′ type-variant UR ×
                Has-well-behaved-zero M semiring-with-meet)
             → Δ ⊢ₛ s ∷ ℕ
             → ▸ s
             → ∃₅ λ m n H (ρ : Wk m n) t → s ↠* ⟨ H , t , ρ , ε ⟩ ×
               Numeral t × ε » Δ ⊢ ⦅ s ⦆ ≡ wk ρ t [ H ]ₕ ∷ ℕ ×
               ▸ ⟨ H , t , ρ , ε ⟩
  redNumeral {s} consistent prop ⊢s ▸s =
    redNumeral′ consistent prop
      (⊩∷ℕ⇔ .proj₁ (reducible-⊩∷ (⊢⦅⦆ {s = s} ⊢s) .proj₂))
      PE.refl ⊢s ▸s

opaque

  -- All closed, well-resourced, well-typed states of type ℕ reduce
  -- to numerals.

  redNumeral-closed :
    ε ⊢ₛ s ∷ ℕ → ▸ s →
    ∃₅ λ m n H (ρ : Wk m n) t → s ↠* ⟨ H , t , ρ , ε ⟩ ×
    Numeral t × ε » ε ⊢ ⦅ s ⦆ ≡ wk ρ t [ H ]ₕ ∷ ℕ ×
    ▸ ⟨ H , t , ρ , ε ⟩
  redNumeral-closed =
    redNumeral ⦃ ε ⦄ (λ _ _ → ¬Empty)
      (λ 0≡0 → ⊥-elim (0≡0 PE.refl))

opaque

  -- Given some assumptions, all well-typed and erased terms of type ℕ reduce to some
  -- numeral and the resulting heap has all grades less than or equal to 𝟘.

  -- Note that some assumptions to this theorem are given as a module parameter.

  soundness-ε :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » Δ)) →
    (k PE.≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M semiring-with-meet) →
    ε » Δ ⊢ t ∷ ℕ →
    𝟘ᶜ ▸ t →
    ∃₅ λ m n H k (ρ : Wk m n) →
    initial t ↠* ⟨ H , sucᵏ k , ρ , ε ⟩ ×
    (ε » Δ ⊢ t ≡ sucᵏ k ∷ ℕ) ×
    H ≤ʰ 𝟘
  soundness-ε {k} {t} {Δ} consistent prop ⊢t ▸t =
    case ▸initial ▸t of λ
      ▸s →
    case redNumeral consistent prop
           (⊢initial ⊢t) ▸s of λ
      (_ , _ , H , ρ , t , d , num , s≡ , ▸s′) →
    case ▸ₛ-inv ▸s′ of λ
      (p , γ , δ , η , ∣ε∣≡ , ▸H , ▸n , ▸ε , γ≤) →
    case Numeral→sucᵏ num of λ
      (k , ≡sucᵏ) →
    case PE.subst (λ x → _ ↠* ⟨ _ , x , _ , _ ⟩) ≡sucᵏ d of λ
      d′ →
    let open RPo ≤ᶜ-poset in
    _ , _ , _ , _ , _
      , d′
      , PE.subst₂ (_ ⊢_≡_∷ ℕ)
          (PE.trans (erasedHeap-subst (wk id _)) (wk-id _))
          (PE.trans (PE.cong (λ x → wk ρ x [ H ]ₕ) ≡sucᵏ)
            (PE.trans (PE.cong (_[ H ]ₕ) (wk-sucᵏ k)) (subst-sucᵏ k)))
          s≡
      , 𝟘▸H→H≤𝟘 (sub ▸H $ begin
          γ                      ≤⟨ γ≤ ⟩
          p ·ᶜ wkConₘ ρ δ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congʳ (∣∣-functional ∣ε∣≡ ε))
                                           (▸ˢ-ε-inv ▸ε) ⟩
          𝟙 ·ᶜ wkConₘ ρ δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
          𝟙 ·ᶜ wkConₘ ρ δ        ≈⟨ ·ᶜ-identityˡ _ ⟩
          wkConₘ ρ δ             ≤⟨ wk-≤ᶜ ρ (inv-usage-numeral ▸n num) ⟩
          wkConₘ ρ 𝟘ᶜ            ≡⟨ wk-𝟘ᶜ ρ ⟩
          𝟘ᶜ                     ∎ )

opaque
  unfolding inlineᵈ

  -- A variant of soundness-ε without the restriction that the
  -- definition context must be empty.
  --
  -- Note that the module telescope contains an assumption of type
  -- Assumptions.

  soundness :
    {Δ : Con Term k}
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » inline-Conᵈ ∇ Δ)) →
    (k PE.≢ 0 →
     No-erased-matches′ type-variant UR ×
     Has-well-behaved-zero M semiring-with-meet) →
    glassify ∇ » Δ ⊢ t ∷ ℕ →
    ▸[ 𝟙ᵐ ] glassify ∇ →
    𝟘ᶜ ▸ t →
    ∃₅ λ m n H k (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ↠* ⟨ H , sucᵏ k , ρ , ε ⟩ ×
    (ε » inline-Conᵈ ∇ Δ ⊢ inlineᵈ ∇ t ≡ sucᵏ k ∷ ℕ) ×
    H ≤ʰ 𝟘
  soundness {t} consistent prop ⊢t ▸∇ ▸t =
    soundness-ε ⦃ ok = or-empty-inline-Conᵈ ⦄ consistent prop
      (PE.subst₃ _⊢_∷_
         (PE.cong (_»_ _) inline-Conᵈ-glassify)
         (inlineᵈ-glassify {t = t}) PE.refl $
       ⊢inlineᵈ∷ ⊢t)
      (▸inlineᵈ ▸∇ ▸t)

opaque
  unfolding inline-Conᵈ

  -- The soundness property above specialised to closed terms.

  -- Note that some assumptions to this theorem are given as a module parameter.

  soundness-closed :
    glassify ∇ » ε ⊢ t ∷ ℕ → ▸[ 𝟙ᵐ ] glassify ∇ → ε ▸ t →
    ∃₅ λ m n H k (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ↠* ⟨ H , sucᵏ k , ρ , ε ⟩ ×
    (ε » ε ⊢ inlineᵈ ∇ t ≡ sucᵏ k ∷ ℕ) ×
    H ≤ʰ 𝟘
  soundness-closed =
    soundness ⦃ ok = ε ⦄ (λ _ _ → ¬Empty) (λ 0≢0 → ⊥-elim (0≢0 PE.refl))

opaque

  -- The soundness property above specialised to open terms.

  -- Note that some assumptions to this theorem are given as a module parameter.

  soundness-open :
    ⦃ No-equality-reflection or-empty Δ ⦄ →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent (ε » inline-Conᵈ ∇ Δ)) →
    No-erased-matches′ type-variant UR →
    Has-well-behaved-zero M semiring-with-meet →
    glassify ∇ » Δ ⊢ t ∷ ℕ → ▸[ 𝟙ᵐ ] glassify ∇ → 𝟘ᶜ ▸ t →
    ∃₅ λ m n H k (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ↠* ⟨ H , sucᵏ k , ρ , ε ⟩ ×
    (ε » inline-Conᵈ ∇ Δ ⊢ inlineᵈ ∇ t ≡ sucᵏ k ∷ ℕ) ×
    H ≤ʰ 𝟘
  soundness-open consistent erased 𝟘-wb = soundness consistent λ _ → erased , 𝟘-wb

opaque

  -- A version of soundness-open

  soundness-open-consistent :
    ⦃ No-equality-reflection or-empty Δ ⦄ →
    Consistent (ε » inline-Conᵈ ∇ Δ) →
    No-erased-matches′ type-variant UR →
    Has-well-behaved-zero M semiring-with-meet →
    glassify ∇ » Δ ⊢ t ∷ ℕ → ▸[ 𝟙ᵐ ] glassify ∇ → 𝟘ᶜ ▸ t →
    ∃₅ λ m n H k (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ↠* ⟨ H , sucᵏ k , ρ , ε ⟩ ×
    (ε » inline-Conᵈ ∇ Δ ⊢ inlineᵈ ∇ t ≡ sucᵏ k ∷ ℕ) ×
    H ≤ʰ 𝟘
  soundness-open-consistent consistent = soundness-open (λ _ → consistent)

opaque

  -- A version of soundness-open

  soundness-open-¬emptyrec₀ :
    ⦃ No-equality-reflection or-empty Δ ⦄ →
    ¬ Emptyrec-allowed 𝟙ᵐ 𝟘 →
    No-erased-matches′ type-variant UR →
    Has-well-behaved-zero M semiring-with-meet →
    glassify ∇ » Δ ⊢ t ∷ ℕ → ▸[ 𝟙ᵐ ] glassify ∇ → 𝟘ᶜ ▸ t →
    ∃₅ λ m n H k (ρ : Wk m n) →
    initial (inlineᵈ ∇ t) ↠* ⟨ H , sucᵏ k , ρ , ε ⟩ ×
    (ε » inline-Conᵈ ∇ Δ ⊢ inlineᵈ ∇ t ≡ sucᵏ k ∷ ℕ) ×
    H ≤ʰ 𝟘
  soundness-open-¬emptyrec₀ ¬ok =
    soundness-open (⊥-elim ∘→ ¬ok)
