------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa
------------------------------------------------------------------------

-- This investigation was prompted by a question asked by an anonymous
-- reviewer.

open import Definition.Modality
open import Definition.Modality.Usage.Restrictions
open import Definition.Typed.Restrictions

module Definition.Sigma
  {a} {M : Set a}
  (𝕄 : Modality M)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄 UR
open import Definition.Modality.Usage.Inversion 𝕄 UR
open import Definition.Modality.Usage.Properties 𝕄 UR
open import Definition.Modality.Usage.Weakening 𝕄 UR
open import Definition.Modality.Substitution.Properties 𝕄 UR

open import Definition.Mode 𝕄

open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Weakening TR as W

open import Definition.Untyped M as U
  hiding (_∷_) renaming (_[_,_] to _[_∣_])
open import Definition.Untyped.Properties M

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n                                   : Nat
  Γ                                   : Con _ _
  A A₁ A₂ B B₁ B₂ C t t₁ t₂ u u₁ u₂ v : Term _
  p q r                               : M
  γ δ                                 : Conₘ _
  m                                   : Mode

------------------------------------------------------------------------
-- Some private lemmas related to the modality

private

  -- Some lemmas used below.

  𝟘≰𝟙→𝟘∧𝟙≢𝟘 : ¬ 𝟘 ≤ 𝟙 → 𝟘 ∧ 𝟙 ≢ 𝟘
  𝟘≰𝟙→𝟘∧𝟙≢𝟘 𝟘≰𝟙 =
    𝟘 ∧ 𝟙 PE.≡ 𝟘  →⟨ flip (PE.subst (_≤ _)) (∧-decreasingʳ 𝟘 𝟙) ⟩
    𝟘 ≤ 𝟙         →⟨ 𝟘≰𝟙 ⟩
    ⊥             □

  𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ :
    ∀ m → ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ → m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m
  𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ = λ where
    𝟘ᵐ _           → PE.refl
    𝟙ᵐ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ → case 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ of λ where
      (inj₁ 𝟘≰𝟙)        → ≉𝟘→⌞⌟≡𝟙ᵐ (𝟘≰𝟙→𝟘∧𝟙≢𝟘 𝟘≰𝟙)
      (inj₂ (inj₁ 𝟙≡𝟘)) → Mode-propositional-if-𝟙≡𝟘 𝟙≡𝟘
      (inj₂ (inj₂ ≢𝟙ᵐ)) → ⊥-elim (≢𝟙ᵐ PE.refl)

  ≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 : 𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 → (∀ p → p ≤ 𝟘) → ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘
  ≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 = λ where
    (inj₁ 𝟙≡𝟘) _  → inj₂ 𝟙≡𝟘
    (inj₂ 𝟙≢𝟘) ≤𝟘 → inj₁
      (𝟘 ≤ 𝟙     →⟨ ≤-antisym (≤𝟘 _) ⟩
       𝟙 PE.≡ 𝟘  →⟨ 𝟙≢𝟘 ⟩
       ⊥         □)

  [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ : (𝟘 ∧ 𝟙) ·ᶜ γ PE.≡ 𝟘ᶜ ∧ᶜ γ
  [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ {γ = γ} =
    (𝟘 ∧ 𝟙) ·ᶜ γ      ≡⟨ ≈ᶜ→≡ (·ᶜ-distribʳ-∧ᶜ _ _ _) ⟩
    𝟘 ·ᶜ γ ∧ᶜ 𝟙 ·ᶜ γ  ≡⟨ ≈ᶜ→≡ (∧ᶜ-cong (·ᶜ-zeroˡ _) (·ᶜ-identityˡ _)) ⟩
    𝟘ᶜ ∧ᶜ γ           ∎
    where
    open Tools.Reasoning.PropositionalEquality

  [𝟘∧𝟙]·≡𝟘∧ : (𝟘 ∧ 𝟙) · p PE.≡ 𝟘 ∧ p
  [𝟘∧𝟙]·≡𝟘∧ {p = p} =
    (𝟘 ∧ 𝟙) · p    ≡⟨ ·-distribʳ-∧ _ _ _ ⟩
    𝟘 · p ∧ 𝟙 · p  ≡⟨ ∧-cong (·-zeroˡ _) (·-identityˡ _) ⟩
    𝟘 ∧ p          ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ·[𝟘∧𝟙]≡𝟘∧ : p · (𝟘 ∧ 𝟙) PE.≡ 𝟘 ∧ p
  ·[𝟘∧𝟙]≡𝟘∧ {p = p} =
    p · (𝟘 ∧ 𝟙)    ≡⟨ ·-distribˡ-∧ _ _ _ ⟩
    p · 𝟘 ∧ p · 𝟙  ≡⟨ ∧-cong (·-zeroʳ _) (·-identityʳ _) ⟩
    𝟘 ∧ p          ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ·[𝟘∧𝟙]·≡𝟘∧· : p · (𝟘 ∧ 𝟙) · q PE.≡ 𝟘 ∧ p · q
  ·[𝟘∧𝟙]·≡𝟘∧· {p = p} {q = q} =
    p · (𝟘 ∧ 𝟙) · q  ≡⟨ ·-congˡ [𝟘∧𝟙]·≡𝟘∧ ⟩
    p · (𝟘 ∧ q)      ≡⟨ ·-distribˡ-∧ _ _ _ ⟩
    p · 𝟘 ∧ p · q    ≡⟨ ∧-congʳ (·-zeroʳ _) ⟩
    𝟘 ∧ p · q        ∎
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Pair constructors

-- If _+_ is pointwise bounded by _∧_, then a usage rule like the one
-- for prodᵣ can be derived for prodₚ.

prodₚᵣₘ :
  (∀ p q → p + q ≤ p ∧ q) →
  γ ▸[ m ᵐ· p ] t →
  δ ▸[ m ] u →
  p ·ᶜ γ +ᶜ δ ▸[ m ] prodₚ p t u
prodₚᵣₘ +≤∧ ▸t ▸u = sub (prodₚₘ ▸t ▸u) (+ᶜ≤ᶜ∧ᶜ +≤∧)

-- If _∧_ is pointwise bounded by _+_, then a usage rule like the one
-- for prodₚ can be derived for prodᵣ.

prodᵣₚₘ :
  (∀ p q → p ∧ q ≤ p + q) →
  γ ▸[ m ᵐ· p ] t →
  δ ▸[ m ] u →
  p ·ᶜ γ ∧ᶜ δ ▸[ m ] prodᵣ p t u
prodᵣₚₘ ∧≤+ ▸t ▸u = sub (prodᵣₘ ▸t ▸u) (∧ᶜ≤ᶜ+ᶜ ∧≤+)

------------------------------------------------------------------------
-- Prodrec for strong Σ-types

-- A definition of prodrec for strong Σ-types.

prodrecₚ : M → Term n → Term (1+ (1+ n)) → Term n
prodrecₚ p t u = u [ fst p t ∣ snd p t ]

------------------------------------------------------------------------
-- Usage lemmas for prodrecₚ

-- A usage lemma for prodrecₚ.

prodrecₚₘ :
  (m ᵐ· r · p PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
  γ ▸[ m ᵐ· r ] t →
  δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
  (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ ▸[ m ] prodrecₚ p t u
prodrecₚₘ {m = m} {r = r} {p = p} {γ = γ} {δ = δ} mrp≡𝟙→p≤𝟙 ▸t ▸u = sub
  (doubleSubstₘ-lemma₁ ▸u
     (sndₘ ▸t)
     (fstₘ (m ᵐ· r) (▸-cong (lemma m) (▸-· ▸t)) (ᵐ·-·-assoc m) mrp≡𝟙→p≤𝟙))
    (begin
       (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ                             ≈⟨ +ᶜ-comm _ _ ⟩
       δ +ᶜ (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ                             ≈⟨ +ᶜ-congˡ $
                                                                      ≈ᶜ-trans
                                                                        (·ᶜ-congʳ $
                                                                         PE.trans
                                                                           (·-congˡ $
                                                                            PE.trans (·-distribˡ-+ _ _ _) $
                                                                            +-congʳ $
                                                                            ·-identityʳ _) $
                                                                         ·-distribˡ-+ _ _ _) $
                                                                      ·ᶜ-distribʳ-+ᶜ _ _ _ ⟩
       δ +ᶜ (⌜ m ⌝ · r) ·ᶜ γ +ᶜ (⌜ m ⌝ · r · p) ·ᶜ γ               ≈˘⟨ +ᶜ-congˡ $ +ᶜ-congˡ $
                                                                       ≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                       ·ᶜ-congʳ $
                                                                       PE.trans (·-assoc _ _ _) $
                                                                       ·-congˡ $
                                                                       PE.trans (·-assoc _ _ _) $
                                                                       ·-congˡ $
                                                                       ·⌜⌞⌟⌝ ⟩
       δ +ᶜ (⌜ m ⌝ · r) ·ᶜ γ +ᶜ (⌜ m ⌝ · r · p) ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ  ∎)
  where
  lemma : ∀ m → ⌞ p ⌟ ·ᵐ m ᵐ· r PE.≡ (m ᵐ· r) ᵐ· p
  lemma 𝟘ᵐ =
    ⌞ p ⌟ ·ᵐ 𝟘ᵐ  ≡⟨ ·ᵐ-zeroʳ-𝟘ᵐ ⟩
    𝟘ᵐ           ∎
    where
    open Tools.Reasoning.PropositionalEquality
  lemma 𝟙ᵐ =
    ⌞ p ⌟ ·ᵐ ⌞ r ⌟  ≡⟨ ·ᵐ-comm ⌞ _ ⌟ _ ⟩
    ⌞ r ⌟ ·ᵐ ⌞ p ⌟  ≡⟨ ⌞⌟·ᵐ ⟩
    ⌞ r · p ⌟       ≡˘⟨ ⌞⌟ᵐ· ⟩
    ⌞ r ⌟ ᵐ· p      ∎
    where
    open Tools.Reasoning.PropositionalEquality

  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A variant of the main usage lemma for prodrecₚ with the mode set
-- to 𝟘ᵐ.

prodrecₚₘ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  γ ▸[ 𝟘ᵐ ] t →
  δ ∙ 𝟘 ∙ 𝟘 ▸[ 𝟘ᵐ ] u →
  δ ▸[ 𝟘ᵐ ] prodrecₚ p t u
prodrecₚₘ-𝟘ᵐ {γ = γ} {δ = δ} {p = p} ⦃ ok = ok ⦄ ▸t ▸u = sub
  (prodrecₚₘ
     (λ ())
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub ▸u $ begin
        δ ∙ 𝟘 · 𝟘 · p ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
        δ ∙ 𝟘 ∙ 𝟘              ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     δ                            ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ δ                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘 ·ᶜ γ +ᶜ δ                  ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroˡ _)) ⟩
     (𝟘 · 𝟘 · (𝟙 + p)) ·ᶜ γ +ᶜ δ  ∎)

-- A variant of the main usage lemma for prodrecₚ with the mode set to
-- 𝟙ᵐ and the quantity p to 𝟘.

prodrecₚₘ-𝟙ᵐ-𝟘 :
  𝟘 ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed →
  γ ▸[ ⌞ r ⌟ ] t →
  δ ∙ 𝟘 ∙ r ▸[ 𝟙ᵐ ] u →
  r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecₚ 𝟘 t u
prodrecₚₘ-𝟙ᵐ-𝟘 {γ = γ} {r = r} {δ = δ} ok ▸t ▸u = sub
  (prodrecₚₘ
     (λ ⌞r𝟘⌟≡𝟙 → case ok of λ where
       (inj₁ 𝟘≤𝟙) → 𝟘≤𝟙
       (inj₂ 𝟘ᵐ-ok) → let open Tools.Reasoning.PropositionalEquality in
         case begin
           𝟘ᵐ[ 𝟘ᵐ-ok ] ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
           𝟘ᵐ?         ≡˘⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
           ⌞ 𝟘 ⌟       ≡˘⟨ ⌞⌟-cong (·-zeroʳ r) ⟩
           ⌞ r · 𝟘 ⌟   ≡⟨ ⌞r𝟘⌟≡𝟙 ⟩
           𝟙ᵐ          ∎
         of λ ())
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub ▸u $ begin
        δ ∙ 𝟙 · r · 𝟘 ∙ 𝟙 · r  ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-congˡ (·-zeroʳ _)) (·-zeroʳ _) ∙ ·-identityˡ _ ⟩
        δ ∙ 𝟘 ∙ r              ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     r ·ᶜ γ +ᶜ δ                  ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-congʳ $
                                      PE.trans (·-identityˡ _) $
                                      PE.trans (·-congˡ (+-identityʳ _)) $
                                      ·-identityʳ _ ⟩
     (𝟙 · r · (𝟙 + 𝟘)) ·ᶜ γ +ᶜ δ  ∎)

-- A variant of the main usage lemma for prodrecₚ with the mode set to
-- 𝟙ᵐ and the quantity p to 𝟙. Note that the context in the conclusion
-- is (r + r) ·ᶜ γ +ᶜ δ, while the corresponding context in the usage
-- rule for prodrec is r ·ᶜ γ +ᶜ δ.

prodrecₚₘ-𝟙ᵐ-𝟙 :
  γ ▸[ ⌞ r ⌟ ] t →
  δ ∙ r ∙ r ▸[ 𝟙ᵐ ] u →
  (r + r) ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecₚ 𝟙 t u
prodrecₚₘ-𝟙ᵐ-𝟙 {γ = γ} {r = r} {δ = δ} ▸t ▸u = sub
  (prodrecₚₘ
     (λ _ → ≤-refl)
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub ▸u $ begin
        δ ∙ 𝟙 · r · 𝟙 ∙ 𝟙 · r  ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-identityˡ _) (·-identityʳ _) ∙ ·-identityˡ _ ⟩
        δ ∙ r ∙ r              ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     (r + r) ·ᶜ γ +ᶜ δ            ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-congʳ $
                                      PE.trans (·-identityˡ _) $
                                      PE.trans (·-distribˡ-+ _ _ _) $
                                      +-cong (·-identityʳ _) (·-identityʳ _) ⟩
     (𝟙 · r · (𝟙 + 𝟙)) ·ᶜ γ +ᶜ δ  ∎)

-- A variant of the previous lemma with the assumption that _∧_ is
-- pointwise bounded by _+_.

prodrecₚₘ-𝟙ᵐ-𝟙-∧≤+ :
  (∀ p q → p ∧ q ≤ p + q) →
  γ ▸[ ⌞ r ⌟ ] t →
  δ ∙ r ∙ r ▸[ 𝟙ᵐ ] u →
  r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecₚ 𝟙 t u
prodrecₚₘ-𝟙ᵐ-𝟙-∧≤+ {γ = γ} {r = r} {δ = δ} ∧≤+ ▸t ▸u = sub
  (prodrecₚₘ-𝟙ᵐ-𝟙 ▸t ▸u)
  (begin
     r ·ᶜ γ +ᶜ δ        ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (∧-idem _)) ⟩
     (r ∧ r) ·ᶜ γ +ᶜ δ  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (∧≤+ _ _)) ⟩
     (r + r) ·ᶜ γ +ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- Typing and equality rules for prodrecₚ

private

  -- A lemma used below.

  ⊢[1,0]↑²[fst,snd]≡ :
    Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢
      C [ prodₚ p (var (x0 +1)) (var x0) ]↑² [ fst p t ∣ snd p t ] ≡
      C [ t ]
  ⊢[1,0]↑²[fst,snd]≡
    {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t = t} ⊢C =
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B                                          →⟨ Σ-η-prod-fst-snd ⟩

    Γ ⊢ prodₚ p (fst p t) (snd p t) ≡ t ∷ Σₚ p , q ▷ A ▹ B            →⟨ substTypeEq (refl ⊢C) ⟩

    Γ ⊢ C [ prodₚ p (fst p t) (snd p t) ] ≡ C [ t ]                   →⟨ PE.subst (_ ⊢_≡ _) (PE.sym $ [1,0]↑²[,] C) ⟩

    Γ ⊢
      C [ prodₚ p (var (x0 +1)) (var x0) ]↑² [ fst p t ∣ snd p t ] ≡
      C [ t ]                                                         □

-- A typing rule for prodrecₚ.

prodrecₚⱼ :
  Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
  Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
  Γ ∙ A ∙ B ⊢ u ∷ C [ prodₚ p (var (x0 +1)) (var x0) ]↑² →
  Γ ⊢ prodrecₚ p t u ∷ C [ t ]
prodrecₚⱼ
  {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t = t} {u = u}
  ⊢C ⊢t ⊢u =                                                      $⟨ fstⱼ ⊢A ⊢B ⊢t
                                                                   , sndⱼ ⊢A ⊢B ⊢t
                                                                   ⟩
  Γ ⊢ fst p t ∷ A ×
  Γ ⊢ snd p t ∷ B [ fst p t ]                                     →⟨ (λ (hyp₁ , hyp₂) →
                                                                        PE.subst (_ ⊢ _ ∷_) (PE.sym (subst-id _)) hyp₁ , hyp₂) ⟩
  Γ ⊢ fst p t ∷ subst idSubst A ×
  Γ ⊢ snd p t ∷ B [ fst p t ]                                     →⟨ (λ (hyp₁ , hyp₂) → (idSubst′ ⊢Γ , hyp₁) , hyp₂) ⟩

  Γ ⊢ˢ
    consSubst (consSubst idSubst (fst p t)) (snd p t) ∷
    Γ ∙ A ∙ B                                                     →⟨ flip (substitutionTerm ⊢u) ⊢Γ ⟩

  Γ ⊢
    prodrecₚ p t u ∷
    C [ prodₚ p (var (x0 +1)) (var x0) ]↑² [ fst p t ∣ snd p t ]  →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t) ⟩

  Γ ⊢ prodrecₚ p t u ∷ C [ t ]                                    □
  where
  ⊢Γ    = wfTerm ⊢t
  ⊢A,⊢B = inversion-ΠΣ (syntacticTerm ⊢t)
  ⊢A    = ⊢A,⊢B .proj₁
  ⊢B    = ⊢A,⊢B .proj₂ .proj₁

-- An equality rule for prodrecₚ.

prodrecₚ-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ] →
  Γ ∙ A ∙ B ⊢ v ∷ C [ prodₚ p (var (x0 +1)) (var x0) ]↑² →
  Σₚ-restriction p q →
  Γ ⊢ prodrecₚ p (prodₚ p t u) v ≡ v [ t ∣ u ] ∷ C [ prodₚ p t u ]
prodrecₚ-β
  {Γ = Γ} {t = t} {A = A} {u = u} {B = B} {v = v} {C = C} {p = p}
  ⊢t ⊢u ⊢v ok =                                                     $⟨ Σ-β₁ ⊢A ⊢B ⊢t ⊢u PE.refl ok
                                                                     , Σ-β₂ ⊢A ⊢B ⊢t ⊢u PE.refl ok
                                                                     ⟩
  Γ ⊢ fst p (prodₚ p t u) ≡ t ∷ A ×
  Γ ⊢ snd p (prodₚ p t u) ≡ u ∷ B [ fst p (prodₚ p t u) ]           →⟨ (λ (hyp₁ , hyp₂) →
                                                                            PE.subst (_ ⊢ _ ≡ _ ∷_) (PE.sym $ subst-id _) hyp₁
                                                                          , conv hyp₂ (substTypeEq (refl ⊢B) hyp₁)) ⟩
  Γ ⊢ fst p (prodₚ p t u) ≡ t ∷ subst idSubst A ×
  Γ ⊢ snd p (prodₚ p t u) ≡ u ∷ B [ t ]                             →⟨ (λ (hyp₁ , hyp₂) →
                                                                          (substRefl (idSubst′ ⊢Γ) , sym hyp₁) , sym hyp₂) ⟩
  Γ ⊢ˢ
    consSubst (consSubst idSubst t) u ≡
    consSubst (consSubst idSubst (fst p (prodₚ p t u)))
      (snd p (prodₚ p t u)) ∷
    Γ ∙ A ∙ B                                                       →⟨ flip (substitutionEqTerm (refl ⊢v)) ⊢Γ ⟩

  Γ ⊢
    v [ t ∣ u ] ≡
    prodrecₚ p (prodₚ p t u) v ∷
    C [ prodₚ p (var (x0 +1)) (var x0) ]↑² [ t ∣ u ]                →⟨ PE.subst (_⊢_≡_∷_ _ _ _) ([1,0]↑²[,] C) ∘→ sym ⟩

  Γ ⊢ prodrecₚ p (prodₚ p t u) v ≡ v [ t ∣ u ] ∷ C [ prodₚ p t u ]  □
  where
  ⊢Γ = wfTerm ⊢t
  ⊢A = syntacticTerm ⊢t
  ⊢B = case wfTerm ⊢v of λ where
         (_ ∙ _ ∙ ⊢B) → ⊢B

-- Another equality rule for prodrecₚ.

prodrecₚ-cong :
  Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
  Γ ⊢ t₁ ≡ t₂ ∷ Σₚ p , q ▷ A ▹ B →
  Γ ∙ A ∙ B ⊢ u₁ ≡ u₂ ∷ C [ prodₚ p (var (x0 +1)) (var x0) ]↑² →
  Γ ⊢ prodrecₚ p t₁ u₁ ≡ prodrecₚ p t₂ u₂ ∷ C [ t₁ ]
prodrecₚ-cong
  {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t₁ = t₁} {t₂ = t₂}
  {u₁ = u₁} {u₂ = u₂} ⊢C t₁≡t₂ u₁≡u₂ =                              $⟨ fst-cong ⊢A ⊢B t₁≡t₂
                                                                     , snd-cong ⊢A ⊢B t₁≡t₂
                                                                     ⟩
  Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A ×
  Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]                          →⟨ (λ (hyp₁ , hyp₂) →
                                                                          PE.subst (_ ⊢ _ ≡ _ ∷_) (PE.sym (subst-id _)) hyp₁ , hyp₂) ⟩
  Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ subst idSubst A ×
  Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]                          →⟨ (λ (hyp₁ , hyp₂) → (substRefl (idSubst′ ⊢Γ) , hyp₁) , hyp₂) ⟩

  Γ ⊢ˢ
    consSubst (consSubst idSubst (fst p t₁)) (snd p t₁) ≡
    consSubst (consSubst idSubst (fst p t₂)) (snd p t₂) ∷
    Γ ∙ A ∙ B                                                       →⟨ flip (substitutionEqTerm u₁≡u₂) ⊢Γ ⟩

  Γ ⊢
    prodrecₚ p t₁ u₁ ≡
    prodrecₚ p t₂ u₂ ∷
    C [ prodₚ p (var (x0 +1)) (var x0) ]↑² [ fst p t₁ ∣ snd p t₁ ]  →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t₁) ⟩

  Γ ⊢ prodrecₚ p t₁ u₁ ≡ prodrecₚ p t₂ u₂ ∷ C [ t₁ ]                □
  where
  ⊢Γ   = wfEqTerm t₁≡t₂
  ⊢t₁  = syntacticEqTerm t₁≡t₂ .proj₂ .proj₁
  ⊢ΓAB = wfEqTerm u₁≡u₂
  ⊢A   = case ⊢ΓAB of λ where
           (_ ∙ ⊢A ∙ _) → ⊢A
  ⊢B   = case ⊢ΓAB of λ where
           (_ ∙ _ ∙ ⊢B) → ⊢B

-- This module does not contain proofs of any reduction rules for
-- prodrecₚ. One might have hoped that the following rules should
-- hold:
--
--   Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
--   Γ ⊢ t ∷ A →
--   Γ ⊢ u ∷ B [ t ] →
--   Γ ∙ A ∙ B ⊢ v ∷ C [ prodₚ p (var (x0 +1)) (var x0) ]↑² →
--   Γ ⊢ prodrecₚ p (prodₚ p t u) v ⇒ v [ t ∣ u ] ∷ C [ prodₚ p t u ]
--
--   Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
--   Γ ∙ A ∙ B ⊢ u ∷ C [ prodᵣ p (var (x0 +1)) (var x0) ]↑² →
--   Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q ▷ A ▹ B →
--   Γ ⊢ prodrecₚ p t₁ u ⇒ prodrecₚ p t₂ u ∷ C [ t₁ ]
--
-- However, the reduction relation only allows reduction in certain
-- places in terms. For instance, it does not include reduction under
-- lambdas. Thus it seems unlikely that the rules above can be proved
-- (but there is no formal proof of this in this module).

------------------------------------------------------------------------
-- An investigation of different potential implementations of a first
-- projection for weak Σ-types

-- A generalised first projection with two extra quantities.

fstᵣ′ : M → M → M → Term n → Term n → Term n
fstᵣ′ r p q A t = prodrec r p q (wk1 A) t (var (x0 +1))

-- An inversion lemma for fstᵣ′.

inv-usage-fstᵣ′ :
  γ ▸[ m ] fstᵣ′ r p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ r ·ᶜ η ×
    η ▸[ m ᵐ· r ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    ⌜ m ⌝ · r · p ≤ ⌜ m ⌝ ×
    ⌜ m ⌝ · r ≤ 𝟘 ×
    Prodrec-restriction r p q
inv-usage-fstᵣ′ {γ = γ} {m = m} {r = r} {p = p} {q = q} ▸fstᵣ′ =
  case inv-usage-prodrec ▸fstᵣ′ of λ {
    (invUsageProdrec {δ = δ} {η = η} {θ = θ} ▸t ▸var ▸A ok γ≤rδ+η) →
  case inv-usage-var ▸var of λ {
    (η≤𝟘 ∙ mrp≤m ∙ mr≤𝟘) →
    δ
  , θ
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ             ≤⟨ γ≤rδ+η ⟩
       r ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ η≤𝟘 ⟩
       r ·ᶜ δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
       r ·ᶜ δ        ∎)
  , ▸t
  , wkUsage⁻¹′ ▸A
  , mrp≤m
  , mr≤𝟘
  , ok }}

-- An inversion lemma for fstᵣ′ with the mode set to 𝟙ᵐ.

inv-usage-fstᵣ′-𝟙ᵐ :
  γ ▸[ 𝟙ᵐ ] fstᵣ′ r p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ r ·ᶜ η ×
    η ▸[ ⌞ r ⌟ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    r · p ≤ 𝟙 ×
    r ≤ 𝟘 ×
    Prodrec-restriction r p q
inv-usage-fstᵣ′-𝟙ᵐ {r = r} {p = p} ▸fstᵣ′ =
  case inv-usage-fstᵣ′ ▸fstᵣ′ of λ {
    (_ , _ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
  _ , _ , leq₁ , ▸t , ▸A ,
  (begin
     r · p      ≡˘⟨ ·-identityˡ _ ⟩
     𝟙 · r · p  ≤⟨ leq₂ ⟩
     𝟙          ∎) ,
  (begin
     r      ≡˘⟨ ·-identityˡ _ ⟩
     𝟙 · r  ≤⟨ leq₃ ⟩
     𝟘      ∎) ,
  ok }
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- If 𝟘 ≰ 𝟙 then no application of fstᵣ′ 𝟘 is well-resourced at
-- mode 𝟙ᵐ.

𝟘≰𝟙→fstᵣ′-𝟘-not-ok :
  ¬ 𝟘 ≤ 𝟙 →
  ¬ γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟘 p q A t
𝟘≰𝟙→fstᵣ′-𝟘-not-ok {γ = γ} {p = p} {q = q} {A = A} {t = t} 𝟘≰𝟙 =
  γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟘 p q A t  →⟨ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ inv-usage-fstᵣ′-𝟙ᵐ ⟩
  𝟘 · p ≤ 𝟙                  →⟨ ≤-trans (≤-reflexive (PE.sym (·-zeroˡ _))) ⟩
  𝟘 ≤ 𝟙                      →⟨ 𝟘≰𝟙 ⟩
  ⊥                          □

-- If 𝟙 ≰ 𝟘 then no application of fstᵣ′ 𝟙 is well-resourced at
-- mode 𝟙ᵐ.

𝟙≰𝟘→fstᵣ′-𝟙-not-ok :
  ¬ 𝟙 ≤ 𝟘 →
  ¬ γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟙 p q A t
𝟙≰𝟘→fstᵣ′-𝟙-not-ok {γ = γ} {p = p} {q = q} {A = A} {t = t} 𝟙≰𝟘 =
  γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟙 p q A t  →⟨ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ inv-usage-fstᵣ′-𝟙ᵐ ⟩
  𝟙 ≤ 𝟘                      →⟨ 𝟙≰𝟘 ⟩
  ⊥                          □

-- An inversion lemma for fstᵣ′ with the mode set to 𝟙ᵐ and either
-- r ≢ 𝟘 or 𝟙 ≡ 𝟘.

inv-usage-fstᵣ′-≢𝟘-𝟙ᵐ :
  r ≢ 𝟘 ⊎ 𝟙 PE.≡ 𝟘 →
  γ ▸[ 𝟙ᵐ ] fstᵣ′ r p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ r ·ᶜ η ×
    η ▸[ 𝟙ᵐ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    r · p ≤ 𝟙 ×
    r ≤ 𝟘 ×
    Prodrec-restriction r p q
inv-usage-fstᵣ′-≢𝟘-𝟙ᵐ r≢𝟘⊎𝟙≡𝟘 ▸fstᵣ′ =
  case inv-usage-fstᵣ′-𝟙ᵐ ▸fstᵣ′ of λ {
    (_ , _ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
  _ , _ , leq₁ ,
  ▸-cong
    (case r≢𝟘⊎𝟙≡𝟘 of λ where
       (inj₁ r≢𝟘) → ≉𝟘→⌞⌟≡𝟙ᵐ r≢𝟘
       (inj₂ 𝟙≡𝟘) → Mode-propositional-if-𝟙≡𝟘 𝟙≡𝟘)
    ▸t ,
  ▸A , leq₂ , leq₃ , ok }

-- An inversion lemma for fstᵣ′ with the mode set to 𝟙ᵐ, r set to
-- 𝟘 ∧ 𝟙, and either 𝟘 ≰ 𝟙 or 𝟙 ≡ 𝟘.

inv-usage-fstᵣ′-𝟘∧𝟙-𝟙ᵐ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 →
  γ ▸[ 𝟙ᵐ ] fstᵣ′ (𝟘 ∧ 𝟙) p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    𝟘 ∧ p ≤ 𝟙 ×
    Prodrec-restriction (𝟘 ∧ 𝟙) p q
inv-usage-fstᵣ′-𝟘∧𝟙-𝟙ᵐ {γ = γ} {p = p} 𝟘≰𝟙⊎𝟙≡𝟘 ▸fstᵣ′ =
  case inv-usage-fstᵣ′-≢𝟘-𝟙ᵐ 𝟘∧𝟙≢𝟘⊎𝟙≡𝟘 ▸fstᵣ′ of λ {
    (η , _ , leq₁ , ▸t , ▸A , leq₂ , _ , ok) →
  _ , _ ,
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ             ≤⟨ leq₁ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ η  ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     𝟘ᶜ ∧ᶜ η       ∎) ,
  ▸t , ▸A ,
  (let open Tools.Reasoning.PartialOrder ≤-poset in begin
     𝟘 ∧ p        ≡˘⟨ [𝟘∧𝟙]·≡𝟘∧ ⟩
     (𝟘 ∧ 𝟙) · p  ≤⟨ leq₂ ⟩
     𝟙            ∎) ,
  ok }
  where
  𝟘∧𝟙≢𝟘⊎𝟙≡𝟘 = case 𝟘≰𝟙⊎𝟙≡𝟘 of λ where
    (inj₁ 𝟘≰𝟙) → inj₁ (𝟘≰𝟙→𝟘∧𝟙≢𝟘 𝟘≰𝟙)
    (inj₂ 𝟙≡𝟘) → inj₂ 𝟙≡𝟘

------------------------------------------------------------------------
-- The first projection for weak Σ-types

-- The first projection.

fstᵣ : M → Term n → Term n → Term n
fstᵣ p = fstᵣ′ (𝟘 ∧ 𝟙) p 𝟘

------------------------------------------------------------------------
-- Inversion lemmas for usage for fstᵣ

-- An inversion lemma for fstᵣ.

inv-usage-fstᵣ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  γ ▸[ m ] fstᵣ p A t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ ×
    Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘
inv-usage-fstᵣ {m = m} {γ = γ} {p = p} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ ▸fstᵣ =
  case inv-usage-fstᵣ′ ▸fstᵣ of λ {
    (η , δ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
  _ , _ ,
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ             ≤⟨ leq₁ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ η  ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     𝟘ᶜ ∧ᶜ η       ∎) ,
  ▸-cong (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ) ▸t ,
  ▸A ,
  (let open Tools.Reasoning.PartialOrder ≤-poset in begin
     𝟘 ∧ ⌜ m ⌝ · p        ≡˘⟨ ·[𝟘∧𝟙]·≡𝟘∧· ⟩
     ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p  ≤⟨ leq₂ ⟩
     ⌜ m ⌝                ∎) ,
  ok }

-- An inversion lemma for fstᵣ with the mode set to 𝟘ᵐ.

inv-usage-fstᵣ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  γ ▸[ 𝟘ᵐ ] fstᵣ p A t →
  ∃ λ δ →
    γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
    δ ▸[ 𝟘ᵐ ] A ×
    Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘
inv-usage-fstᵣ-𝟘ᵐ {γ = γ} ▸fstᵣ =
  case inv-usage-fstᵣ (inj₂ (inj₂ (λ ()))) ▸fstᵣ of λ {
    (η , _ , leq₁ , ▸t , ▸A , leq₂ , ok) →
  _ ,
  (begin
     γ        ≤⟨ leq₁ ⟩
     𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
     η        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
     𝟘ᶜ       ∎) ,
  (sub (▸-· {m′ = 𝟘ᵐ} ▸t) $ begin
     𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘 ·ᶜ η  ∎) ,
  ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A , ok }
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for fstᵣ with the mode set to 𝟙ᵐ.

inv-usage-fstᵣ-𝟙ᵐ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 →
  γ ▸[ 𝟙ᵐ ] fstᵣ p A t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    𝟘 ∧ p ≤ 𝟙 ×
    Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘
inv-usage-fstᵣ-𝟙ᵐ {p = p} 𝟘≰𝟙⊎𝟙≡𝟘 ▸fstᵣ =
  case inv-usage-fstᵣ 𝟘≰𝟙⊎𝟙≡𝟘⊎𝟙ᵐ≢𝟙ᵐ ▸fstᵣ of λ {
    (_ , _ , leq₁ , ▸t , ▸A , leq₂ , ok) →
  _ , _ , leq₁ , ▸t , ▸A ,
  (begin
     𝟘 ∧ p      ≡˘⟨ ∧-congˡ (·-identityˡ _) ⟩
     𝟘 ∧ 𝟙 · p  ≤⟨ leq₂ ⟩
     𝟙          ∎) ,
  ok }
  where
  open Tools.Reasoning.PartialOrder ≤-poset

  𝟘≰𝟙⊎𝟙≡𝟘⊎𝟙ᵐ≢𝟙ᵐ = case 𝟘≰𝟙⊎𝟙≡𝟘 of λ where
    (inj₁ 𝟘≰𝟙) → inj₁ 𝟘≰𝟙
    (inj₂ 𝟙≡𝟘) → inj₂ (inj₁ 𝟙≡𝟘)

------------------------------------------------------------------------
-- Usage lemmas for fstᵣ

-- A usage lemma for fstᵣ.

fstᵣₘ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ →
  Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ m ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  𝟘ᶜ ∧ᶜ γ ▸[ m ] fstᵣ p A t
fstᵣₘ {m = m} {p = p} {γ = γ} {δ = δ} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ 𝟘∧mp≤m ok ▸t ▸A = sub
  (prodrecₘ
     (▸-cong (PE.sym (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)) ▸t)
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub var $ begin
        𝟘ᶜ ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]·≡𝟘∧· ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
        𝟘ᶜ ∙ 𝟘 ∧ ⌜ m ⌝ · p ∙ 𝟘 ∧ ⌜ m ⌝              ≤⟨ ≤ᶜ-refl ∙ 𝟘∧mp≤m ∙ ∧-decreasingˡ _ _ ⟩
        𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘                              ∎)
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (wkUsage (step id) ▸A) $ begin
        δ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
        δ ∙ 𝟘            ∎)
     ok)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ ∧ᶜ γ             ≡˘⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

-- A usage lemma for fstᵣ with the mode set to 𝟘ᵐ.

fstᵣₘ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟘ᵐ ] t →
  δ ▸[ 𝟘ᵐ ] A →
  γ ▸[ 𝟘ᵐ ] fstᵣ p A t
fstᵣₘ-𝟘ᵐ {p = p} {γ = γ} {δ = δ} ok ▸t ▸A = sub
  (fstᵣₘ
     (inj₂ (inj₂ (λ ())))
     (let open Tools.Reasoning.PartialOrder ≤-poset in begin
        𝟘 ∧ 𝟘 · p  ≡⟨ ∧-congˡ (·-zeroˡ _) ⟩
        𝟘 ∧ 𝟘      ≡⟨ ∧-idem _ ⟩
        𝟘          ∎)
     ok
     ▸t
     (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (▸-𝟘ᵐ ▸t) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)

-- A usage lemma for fstᵣ with the mode set to 𝟙ᵐ.

fstᵣₘ-𝟙ᵐ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 →
  𝟘 ∧ p ≤ 𝟙 →
  Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟙ᵐ ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  𝟘ᶜ ∧ᶜ γ ▸[ 𝟙ᵐ ] fstᵣ p A t
fstᵣₘ-𝟙ᵐ {p = p} 𝟘≰𝟙⊎𝟙≢𝟘 𝟘∧p≤𝟙 = fstᵣₘ
  (case 𝟘≰𝟙⊎𝟙≢𝟘 of λ where
     (inj₁ 𝟘≰𝟙) → inj₁ 𝟘≰𝟙
     (inj₂ 𝟙≢𝟘) → inj₂ (inj₁ 𝟙≢𝟘))
  (begin
     𝟘 ∧ 𝟙 · p  ≡⟨ ∧-congˡ (·-identityˡ _) ⟩
     𝟘 ∧ p      ≤⟨ 𝟘∧p≤𝟙 ⟩
     𝟙          ∎)
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- A usage lemma for fstᵣ with the mode set to 𝟙ᵐ and the assumption
-- that 𝟘 is the largest quantity.

fstᵣₘ-𝟙ᵐ-≤𝟘 :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p → p ≤ 𝟘) →
  p ≤ 𝟙 →
  Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟙ᵐ ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  γ ▸[ 𝟙ᵐ ] fstᵣ p A t
fstᵣₘ-𝟙ᵐ-≤𝟘 {p = p} {γ = γ} 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘 p≤𝟙 ok ▸t ▸A = sub
  (fstᵣₘ-𝟙ᵐ
     (≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘)
     (let open Tools.Reasoning.PartialOrder ≤-poset in begin
        𝟘 ∧ p  ≤⟨ ∧-decreasingʳ _ _ ⟩
        p      ≤⟨ p≤𝟙 ⟩
        𝟙      ∎)
     ok
     ▸t
     ▸A)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (≤ᶜ𝟘ᶜ (≤𝟘 _)) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)

-- A usage lemma for fstᵣ with the mode set to 𝟙ᵐ and the assumption
-- that _+_ is pointwise bounded by _∧_.

fstᵣₘ-𝟙ᵐ-∧≤+ :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p q → p + q ≤ p ∧ q) →
  p ≤ 𝟙 →
  Prodrec-restriction (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟙ᵐ ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  γ ▸[ 𝟙ᵐ ] fstᵣ p A t
fstᵣₘ-𝟙ᵐ-∧≤+ 𝟙≡𝟘⊎𝟙≢𝟘 +≤∧ = fstᵣₘ-𝟙ᵐ-≤𝟘 𝟙≡𝟘⊎𝟙≢𝟘 (+≤∧→≤𝟘 +≤∧)

------------------------------------------------------------------------
-- Some private lemmas related to wk1 and wk1Subst

private

  -- Some lemmas used below.

  ⊢wk1 :
    Γ ⊢ A →
    Γ ⊢ B →
    Γ ∙ A ⊢ wk1 B
  ⊢wk1 ⊢A = W.wk (step id) (wf ⊢A ∙ ⊢A)

  Σ⊢wk1 :
    Γ ∙ A ⊢ B →
    Σᵣ-restriction p q →
    Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A
  Σ⊢wk1 ⊢B ok = ⊢wk1 (ΠΣⱼ ⊢A ⊢B ok) ⊢A
    where
    ⊢A = case wf ⊢B of λ where
           (_ ∙ ⊢A) → ⊢A

  ⊢wk1-wk1 :
    Γ ∙ A ⊢ B →
    Γ ∙ A ∙ B ⊢ wk1 (wk1 A)
  ⊢wk1-wk1 ⊢B = W.wk (step id) ⊢ΓAB (W.wk (step id) ⊢ΓA ⊢A)
    where
    ⊢ΓA  = wf ⊢B
    ⊢A   = case ⊢ΓA of λ where
             (_ ∙ ⊢A) → ⊢A
    ⊢ΓAB = ⊢ΓA ∙ ⊢B

  ⊢wk1[]≡ :
    Γ ⊢ A →
    Γ ⊢ wk1 A [ t ] ≡ A
  ⊢wk1[]≡ {Γ = Γ} {A = A} {t = t} =
    Γ ⊢ A                  →⟨ refl ⟩
    (Γ ⊢ A ≡ A)            →⟨ PE.subst (_ ⊢_≡ _) (PE.sym (wk1-sgSubst _ _)) ⟩
    (Γ ⊢ wk1 A [ t ] ≡ A)  □

  ⊢wk1≡ :
    Γ ⊢ A →
    Γ ⊢ B →
    Γ ∙ A ⊢ wk1 B ≡ subst (wk1Subst idSubst) B
  ⊢wk1≡ {Γ = Γ} {A = A} {B = B} ⊢A =
    Γ ⊢ B                                         →⟨ ⊢wk1 ⊢A ⟩
    Γ ∙ A ⊢ wk1 B                                 →⟨ refl ⟩
    (Γ ∙ A ⊢ wk1 B ≡ wk1 B)                       →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl lemma ⟩
    (Γ ∙ A ⊢ wk1 B ≡ subst (wk1Subst idSubst) B)  □
    where
    open Tools.Reasoning.PropositionalEquality

    lemma =
      wk1 B                        ≡⟨ wk≡subst _ _ ⟩
      subst (toSubst (step id)) B  ≡⟨⟩
      subst (wk1Subst idSubst) B   ∎

  ⊢wk1-wk1≡ :
    Γ ∙ A ⊢ B →
    Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ subst (wk1Subst (wk1Subst idSubst)) A
  ⊢wk1-wk1≡ {Γ = Γ} {A = A} {B = B} =
    Γ ∙ A ⊢ B                                                          →⟨ ⊢wk1-wk1 ⟩
    Γ ∙ A ∙ B ⊢ wk1 (wk1 A)                                            →⟨ refl ⟩
    (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 (wk1 A))                            →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl lemma ⟩
    (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ subst (wk1Subst (wk1Subst idSubst)) A)  □
    where
    open Tools.Reasoning.PropositionalEquality

    lemma =
      wk1 (wk1 A)                            ≡⟨ wk1-wk _ _ ⟩
      U.wk (step (step id)) A                ≡⟨ wk≡subst _ _ ⟩
      subst (toSubst (step (step id))) A     ≡⟨⟩
      subst (wk1Subst (wk1Subst idSubst)) A  ∎

  ⊢ˢwk1Subst-idSubst :
    Γ ⊢ A →
    Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ
  ⊢ˢwk1Subst-idSubst {Γ = Γ} {A = A} ⊢A =
                                   $⟨ idSubst′ ⊢Γ ⟩
    Γ ⊢ˢ idSubst ∷ Γ               →⟨ wk1Subst′ ⊢Γ ⊢Γ ⊢A ⟩
    Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ  □
    where
    ⊢Γ = wf ⊢A

  ⊢ˢwk1Subst-wk1Subst-idSubst :
    Γ ∙ A ⊢ B →
    Γ ∙ A ∙ B ⊢ˢ wk1Subst (wk1Subst idSubst) ∷ Γ
  ⊢ˢwk1Subst-wk1Subst-idSubst {Γ = Γ} {A = A} {B = B} ⊢B =
    case ⊢ΓA of λ { (⊢Γ ∙ ⊢A) →
                                                  $⟨ ⊢ˢwk1Subst-idSubst ⊢A ⟩
    Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ                 →⟨ wk1Subst′ ⊢Γ ⊢ΓA ⊢B ⟩
    Γ ∙ A ∙ B ⊢ˢ wk1Subst (wk1Subst idSubst) ∷ Γ  □ }
    where
    ⊢ΓA = wf ⊢B

------------------------------------------------------------------------
-- Typing rules for fstᵣ

private

  -- A lemma used below.

  1∷wk1[1,0] :
    Γ ∙ A ⊢ B →
    Γ ∙ A ∙ B ⊢ var (x0 +1) ∷ wk1 A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
  1∷wk1[1,0] {Γ = Γ} {A = A} {B = B} {p = p} ⊢B =   $⟨ ⊢B ⟩

    Γ ∙ A ⊢ B                                       →⟨ ⊢wk1-wk1 ⟩

    Γ ∙ A ∙ B ⊢ wk1 (wk1 A)                         →⟨ refl ⟩

    (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 (wk1 A))         →⟨ PE.subst (_⊢_≡_ _ _) (PE.sym wk1-[]↑²) ⟩

    (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡
       wk1 A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²)  →⟨ conv (var (wf ⊢B ∙ ⊢B) (there here)) ⟩

    (Γ ∙ A ∙ B ⊢ var (x0 +1) ∷
       wk1 A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²)  □

-- A typing rule for fstᵣ.

fstᵣⱼ :
  Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
  Γ ⊢ fstᵣ p A t ∷ A
fstᵣⱼ {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t =              $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
  (Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A) ×
  Γ ∙ A ∙ B ⊢ var (x0 +1) ∷ wk1 A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) →
                                                                              prodrecⱼ ⊢A ⊢B hyp₁ ⊢t hyp₂ ok) ⟩

  Γ ⊢ fstᵣ p A t ∷ wk1 A [ t ]                                          →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

  Γ ⊢ fstᵣ p A t ∷ A                                                    □
  where
  ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
  ⊢A       = ⊢A,⊢B,ok .proj₁
  ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
  ok       = ⊢A,⊢B,ok .proj₂ .proj₂

-- A reduction rule for fstᵣ.

fstᵣ-β-⇒ :
  Γ ∙ A ⊢ B →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ] →
  Σᵣ-restriction p q →
  Γ ⊢ fstᵣ p A (prodᵣ p t u) ⇒ t ∷ A
fstᵣ-β-⇒
  {Γ = Γ} {A = A} {B = B} {t = t} {u = u} {p = p} {q = q} ⊢B ⊢t ⊢u ok =
                                                                        $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
  (Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A) ×
  Γ ∙ A ∙ B ⊢ var (x0 +1) ∷ wk1 A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-β ⊢A ⊢B hyp₁ ⊢t ⊢u hyp₂ PE.refl ok) ⟩

  Γ ⊢ fstᵣ p A (prodᵣ p t u) ⇒ t ∷ wk1 A [ prodᵣ p t u ]                →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

  Γ ⊢ fstᵣ p A (prodᵣ p t u) ⇒ t ∷ A                                    □
  where
  ⊢A = syntacticTerm ⊢t

-- Another reduction rule for fstᵣ.

fstᵣ-subst :
  Γ ∙ A ⊢ B →
  Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q ▷ A ▹ B →
  Γ ⊢ fstᵣ p A t₁ ⇒ fstᵣ p A t₂ ∷ A
fstᵣ-subst
  {Γ = Γ} {A = A} {B = B} {t₁ = t₁} {t₂ = t₂} {p = p} {q = q} ⊢B t₁⇒t₂ =
                                                                        $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
  (Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A) ×
  Γ ∙ A ∙ B ⊢ var (x0 +1) ∷ wk1 A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-subst ⊢A ⊢B hyp₁ hyp₂ t₁⇒t₂ ok) ⟩

  Γ ⊢ fstᵣ p A t₁ ⇒ fstᵣ p A t₂ ∷ wk1 A [ t₁ ]                          →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

  Γ ⊢ fstᵣ p A t₁ ⇒ fstᵣ p A t₂ ∷ A                                     □
  where
  ⊢A = case wf ⊢B of λ where
         (_ ∙ ⊢A) → ⊢A
  ok = ⊢∷ΠΣ→ΠΣ-restriction $
       syntacticRedTerm (redMany t₁⇒t₂) .proj₂ .proj₁

-- An equality rule for fstᵣ.

fstᵣ-β-≡ :
  Γ ∙ A ⊢ B →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ] →
  Σᵣ-restriction p q →
  Γ ⊢ fstᵣ p A (prodᵣ p t u) ≡ t ∷ A
fstᵣ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (fstᵣ-β-⇒ ⊢B ⊢t ⊢u ok)

-- Another equality rule for fstᵣ.

fstᵣ-cong :
  Γ ⊢ A₁ ≡ A₂ →
  Γ ∙ A₁ ⊢ B₁ →
  Γ ⊢ t₁ ≡ t₂ ∷ Σᵣ p , q ▷ A₁ ▹ B₁ →
  Γ ⊢ fstᵣ p A₁ t₁ ≡ fstᵣ p A₂ t₂ ∷ A₁
fstᵣ-cong
  {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {t₁ = t₁} {t₂ = t₂}
  {p = p} {q = q} A₁≡A₂ ⊢B₁ t₁≡t₂ =                $⟨ W.wkEq (step id) (wfEq A₁≡A₂ ∙ ΠΣⱼ ⊢A₁ ⊢B₁ ok) A₁≡A₂
                                                    , 1∷wk1[1,0] ⊢B₁
                                                    ⟩
  (Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢ wk1 A₁ ≡ wk1 A₂) ×
  Γ ∙ A₁ ∙ B₁ ⊢
    var (x0 +1) ∷
    wk1 A₁ [ prodᵣ p (var (x0 +1)) (var x0) ]↑²    →⟨ (λ (hyp₁ , hyp₂) → prodrec-cong ⊢A₁ ⊢B₁ hyp₁ t₁≡t₂ (refl hyp₂) ok) ⟩

  Γ ⊢ fstᵣ p A₁ t₁ ≡ fstᵣ p A₂ t₂ ∷ wk1 A₁ [ t₁ ]  →⟨ flip conv (⊢wk1[]≡ ⊢A₁) ⟩

  Γ ⊢ fstᵣ p A₁ t₁ ≡ fstᵣ p A₂ t₂ ∷ A₁             □
  where
  ⊢A₁ = syntacticEq A₁≡A₂ .proj₁
  ok  = ⊢∷ΠΣ→ΠΣ-restriction $
        syntacticEqTerm t₁≡t₂ .proj₂ .proj₁

------------------------------------------------------------------------
-- Some private lemmas related to fstᵣ

private

  -- Some lemmas used below.

  fstᵣ-0[] : fstᵣ p (wk1 A) (var x0) [ t ] PE.≡ fstᵣ p A t
  fstᵣ-0[] {A = A} {t = t} = PE.cong (λ A → prodrec _ _ _ A _ _) $
    subst (liftSubst (sgSubst t)) (wk1 (wk1 A))  ≡⟨ subst-wk (wk1 A) ⟩
    subst (wk1 ∘→ sgSubst t) (wk1 A)             ≡⟨ wk1-tail A ⟩
    subst (wk1Subst idSubst) A                   ≡˘⟨ wk≡subst _ _ ⟩
    wk1 A                                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

  [fstᵣ] :
    ∀ B → B [ fstᵣ p A t ] PE.≡ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]
  [fstᵣ] {p = p} {A = A} {t = t} B =
    B [ fstᵣ p A t ]                                            ≡˘⟨ (flip substVar-to-subst B λ where
                                                                       x0     → fstᵣ-0[]
                                                                       (_ +1) → PE.refl) ⟩
    subst
      (sgSubst t ₛ•ₛ
       consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A) (var x0)))
      B                                                         ≡˘⟨ substCompEq B ⟩

    B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ⊢≡[fstᵣ] :
    Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
    Γ ⊢ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ] ≡ B [ fstᵣ p A t ]
  ⊢≡[fstᵣ] {Γ = Γ} {t = t} {p = p} {A = A} {B = B} ⊢t =            $⟨ substitution ⊢B (singleSubst (fstᵣⱼ ⊢t)) ⊢Γ ⟩
    Γ ⊢ B [ fstᵣ p A t ]                                           →⟨ refl ⟩
    (Γ ⊢ B [ fstᵣ p A t ] ≡ B [ fstᵣ p A t ])                      →⟨ PE.subst₂ (_ ⊢_≡_) ([fstᵣ] B) PE.refl ⟩
    (Γ ⊢ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ] ≡ B [ fstᵣ p A t ])  □
    where
    ⊢Γ = wfTerm ⊢t
    ⊢B = inversion-ΠΣ (syntacticTerm ⊢t) .proj₂ .proj₁

  [fstᵣ-0]↑[1,0]↑² :
    ∀ B →
    B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
      PE.≡
    B [ fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var (x0 +1)) (var x0)) ]↑²
  [fstᵣ-0]↑[1,0]↑² {p = p} {A = A} B =
    B [ fstᵣ p (wk1 A) (var x0) ]↑
      [ prodᵣ p (var (x0 +1)) (var x0) ]↑²                         ≡⟨ substCompEq B ⟩

    subst
      (consSubst (wk1Subst (wk1Subst idSubst))
         (prodᵣ p (var (x0 +1)) (var x0)) ₛ•ₛ
       consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A) (var x0)))
      B                                                            ≡⟨ (flip substVar-to-subst B λ where
                                                                         x0     → PE.refl
                                                                         (_ +1) → PE.refl) ⟩
    B [ prodrec (𝟘 ∧ 𝟙) p 𝟘
          (subst
             (liftSubst $
              consSubst (wk1Subst (wk1Subst idSubst)) $
              prodᵣ p (var (x0 +1)) (var x0)) $
           wk1 (wk1 A))
          (prodᵣ p (var (x0 +1)) (var x0))
          (var (x0 +1)) ]↑²                                        ≡⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                      PE.trans (wk1-tail (wk1 A)) $
                                                                      wk1-tail A ⟩
    B [ prodrec (𝟘 ∧ 𝟙) p 𝟘
          (subst (wk1Subst (wk1Subst (wk1Subst idSubst))) A)
          (prodᵣ p (var (x0 +1)) (var x0))
          (var (x0 +1)) ]↑²                                        ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                       PE.trans (PE.cong (subst _) $ substCompEq A) $
                                                                       substCompEq A ⟩
    B [ prodrec (𝟘 ∧ 𝟙) p 𝟘
          (subst (wk1Subst idSubst) $
           subst (wk1Subst idSubst) $
           subst (wk1Subst idSubst) A)
          (prodᵣ p (var (x0 +1)) (var x0))
          (var (x0 +1)) ]↑²                                        ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                       PE.trans (wk≡subst _ _) $
                                                                       PE.trans (PE.cong (subst _) $ wk≡subst _ (wk1 A)) $
                                                                       PE.cong (subst _) $ PE.cong (subst _) $ wk≡subst _ A ⟩
    B [ fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var (x0 +1)) (var x0)) ]↑²  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ⊢≡[fstᵣ-0]↑[1,0]↑² :
    Γ ∙ A ⊢ B →
    Σᵣ-restriction p q →
    Γ ∙ A ∙ B ⊢
      wk1 B ≡
      B [ fstᵣ p (wk1 A) (var x0) ]↑
        [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
  ⊢≡[fstᵣ-0]↑[1,0]↑² {Γ = Γ} {A = A} {B = B} {p = p} ⊢B ok =         $⟨ substRefl (⊢ˢwk1Subst-wk1Subst-idSubst ⊢B) , lemma ⟩
    Γ ∙ A ∙ B ⊢ˢ
      consSubst (wk1Subst (wk1Subst idSubst)) (var (x0 +1)) ≡
      consSubst (wk1Subst (wk1Subst idSubst))
        (fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var (x0 +1)) (var x0))) ∷
      Γ ∙ A                                                          →⟨ flip (substitutionEq (refl ⊢B)) ⊢ΓAB ⟩

    Γ ∙ A ∙ B ⊢
      B [ var (x0 +1) ]↑² ≡
      B [ fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var (x0 +1)) (var x0)) ]↑²  →⟨ PE.subst₂ (_ ⊢_≡_) [1]↑² (PE.sym $ [fstᵣ-0]↑[1,0]↑² B) ⟩

    Γ ∙ A ∙ B ⊢
      wk1 B ≡
      B [ fstᵣ p (wk1 A) (var x0) ]↑
        [ prodᵣ p (var (x0 +1)) (var x0) ]↑²                         □
    where
    ⊢ΓAB = wf ⊢B ∙ ⊢B

    lemma =                                                       $⟨ ⊢wk1 ⊢B ⊢B ⟩

      (Γ ∙ A ∙ B ⊢ wk1 B)                                         →⟨ refl ⟩

      Γ ∙ A ∙ B ⊢ wk1 B ≡ wk1 B                                   →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl (PE.sym (wk1-sgSubst (wk1 B) _)) ⟩

      Γ ∙ A ∙ B ⊢ wk1 B ≡ wk1 (wk1 B) [ var (x0 +1) ]             →⟨ conv (var ⊢ΓAB here) ⟩

      (Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 (wk1 B) [ var (x0 +1) ])          →⟨ (λ ⊢0 → ⊢wk1-wk1 (⊢wk1-wk1 ⊢B) , var ⊢ΓAB (there here) , ⊢0) ⟩

      (Γ ∙ A ∙ B ∙ wk1 (wk1 A) ⊢ wk1 (wk1 B)) ×
      (Γ ∙ A ∙ B ⊢ var (x0 +1) ∷ wk1 (wk1 A)) ×
      (Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 (wk1 B) [ var (x0 +1) ])          →⟨ (λ (⊢B , ⊢1 , ⊢0) → fstᵣ-β-≡ ⊢B ⊢1 ⊢0 ok) ⟩

      (Γ ∙ A ∙ B ⊢
         fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var (x0 +1)) (var x0)) ≡
         var (x0 +1) ∷
         wk1 (wk1 A))                                             →⟨ flip _⊢_≡_∷_.conv (⊢wk1-wk1≡ ⊢B) ∘→ _⊢_≡_∷_.sym ⟩

      (Γ ∙ A ∙ B ⊢
         var (x0 +1) ≡
         fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var (x0 +1)) (var x0)) ∷
         subst (wk1Subst (wk1Subst idSubst)) A)                   □

  ⊢[fstᵣ-0]↑≡[fstᵣ-0]↑ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
    Σᵣ-restriction p q →
    Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
      B₁ [ fstᵣ p (wk1 A₁) (var x0) ]↑ ≡
      B₂ [ fstᵣ p (wk1 A₂) (var x0) ]↑
  ⊢[fstᵣ-0]↑≡[fstᵣ-0]↑
    {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} {p = p} {q = q}
    A₁≡A₂ B₁≡B₂ ok =                                             $⟨ refl (var ⊢ΓΣA₁B₁ here) ⟩
    Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
      var x0 ≡
      var x0 ∷
      wk1 (Σᵣ p , q ▷ A₁ ▹ B₁)                                   →⟨ fstᵣ-cong
                                                                      (wkEq (step id) ⊢ΓΣA₁B₁ A₁≡A₂)
                                                                      (W.wk (lift (step id)) (⊢ΓΣA₁B₁ ∙ ⊢wk1 ⊢ΣA₁B₁ ⊢A₁) ⊢B₁) ⟩
    Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
      fstᵣ p (wk1 A₁) (var x0) ≡
      fstᵣ p (wk1 A₂) (var x0) ∷
      wk1 A₁                                                     →⟨ flip conv (⊢wk1≡ ⊢ΣA₁B₁ ⊢A₁) ⟩

    Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
      fstᵣ p (wk1 A₁) (var x0) ≡
      fstᵣ p (wk1 A₂) (var x0) ∷
      subst (wk1Subst idSubst) A₁                                →⟨ substRefl (⊢ˢwk1Subst-idSubst ⊢ΣA₁B₁) ,_ ⟩

    Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢ˢ
      consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A₁) (var x0)) ≡
      consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A₂) (var x0)) ∷
      Γ ∙ A₁                                                     →⟨ flip (substitutionEq B₁≡B₂) ⊢ΓΣA₁B₁ ⟩

    Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
      B₁ [ fstᵣ p (wk1 A₁) (var x0) ]↑ ≡
      B₂ [ fstᵣ p (wk1 A₂) (var x0) ]↑                           □
    where
    ⊢A₁     = syntacticEq A₁≡A₂ .proj₁
    ⊢B₁     = syntacticEq B₁≡B₂ .proj₁
    ⊢ΣA₁B₁  = ΠΣⱼ ⊢A₁ ⊢B₁ ok
    ⊢ΓΣA₁B₁ = wf ⊢A₁ ∙ ⊢ΣA₁B₁

  ⊢[fstᵣ-0]↑ :
    Γ ∙ A ⊢ B →
    Σᵣ-restriction p q →
    Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ B [ fstᵣ p (wk1 A) (var x0) ]↑
  ⊢[fstᵣ-0]↑ ⊢B ok =
    syntacticEq (⊢[fstᵣ-0]↑≡[fstᵣ-0]↑ (refl ⊢A) (refl ⊢B) ok) .proj₁
    where
    ⊢A = case wf ⊢B of λ where
           (_ ∙ ⊢A) → ⊢A

  ⊢0∷[fstᵣ-0]↑[1,0]↑² :
    Γ ∙ A ⊢ B →
    Σᵣ-restriction p q →
    Γ ∙ A ∙ B ⊢
      var x0 ∷
      B [ fstᵣ p (wk1 A) (var x0) ]↑
        [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
  ⊢0∷[fstᵣ-0]↑[1,0]↑² {Γ = Γ} {A = A} {B = B} {p = p} ⊢B ok =
                                              $⟨ var (wf ⊢B ∙ ⊢B) here ⟩

    Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 B                →⟨ flip conv (⊢≡[fstᵣ-0]↑[1,0]↑² ⊢B ok) ⟩

    Γ ∙ A ∙ B ⊢
      var x0 ∷
      B [ fstᵣ p (wk1 A) (var x0) ]↑
        [ prodᵣ p (var (x0 +1)) (var x0) ]↑²  □

------------------------------------------------------------------------
-- The second projection for weak Σ-types

-- The second projection.

sndᵣ : M → M → Term n → Term (1+ n) → Term n → Term n
sndᵣ p q A B t =
  prodrec (𝟘 ∧ 𝟙) p q (B [ fstᵣ p (wk1 A) (var x0) ]↑) t (var x0)

------------------------------------------------------------------------
-- Inversion lemmas for usage for sndᵣ

-- An inversion lemma for sndᵣ.

inv-usage-sndᵣ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  ∀ B →
  γ ▸[ m ] sndᵣ p q A B t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
    δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ ×
    Prodrec-restriction (𝟘 ∧ 𝟙) p q
inv-usage-sndᵣ {γ = γ} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ _ ▸sndᵣ =
  case inv-usage-prodrec ▸sndᵣ of λ {
    (invUsageProdrec {δ = δ} {η = η} {θ = θ} ▸t ▸var ▸B ok γ≤[𝟘∧𝟙]δ+η) →
  case inv-usage-var ▸var of λ {
    (η≤𝟘 ∙ _ ∙ _) →
    δ
  , θ
  , (begin
       γ                   ≤⟨ γ≤[𝟘∧𝟙]δ+η ⟩
       (𝟘 ∧ 𝟙) ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ η≤𝟘 ⟩
       (𝟘 ∧ 𝟙) ·ᶜ δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ δ        ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
       𝟘ᶜ ∧ᶜ δ             ∎)
  , ▸-cong (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ) ▸t
  , ▸B
  , ok }}
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for sndᵣ with the mode set to 𝟘ᵐ.

inv-usage-sndᵣ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  ∀ B →
  γ ▸[ 𝟘ᵐ ] sndᵣ p q A B t →
  ∃ λ δ →
    γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
    δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstᵣ p (wk1 A) (var x0) ]↑ ×
    Prodrec-restriction (𝟘 ∧ 𝟙) p q
inv-usage-sndᵣ-𝟘ᵐ {γ = γ} {q = q} ⦃ ok = 𝟘ᵐ-ok ⦄ B ▸sndᵣ =
  case inv-usage-sndᵣ (inj₂ (inj₂ (λ ()))) B ▸sndᵣ of λ {
    (η , δ , leq , ▸t , ▸B , ok) →
    _
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ        ≤⟨ leq ⟩
       𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
       η        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
       𝟘ᶜ       ∎)
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
     sub (▸-· {m′ = 𝟘ᵐ} ▸t) $ begin
       𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
       𝟘 ·ᶜ η  ∎)
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
     sub (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸B) $ begin
       δ ∙ 𝟘            ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
       δ ∙ 𝟘 · q        ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ (PE.cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
       δ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ∎)
  , ok }

------------------------------------------------------------------------
-- Usage lemmas for sndᵣ

-- A usage lemma for sndᵣ.

sndᵣₘ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  Prodrec-restriction (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ m ] t →
  δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  𝟘ᶜ ∧ᶜ γ ▸[ m ] sndᵣ p q A B t
sndᵣₘ {m = m} {p = p} {γ = γ} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ ok _ ▸t ▸B = sub
  (prodrecₘ
     (▸-cong (PE.sym (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)) ▸t)
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub var $ begin
        𝟘ᶜ ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]·≡𝟘∧· ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
        𝟘ᶜ ∙ 𝟘 ∧ ⌜ m ⌝ · p ∙ 𝟘 ∧ ⌜ m ⌝              ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingˡ _ _ ∙ ∧-decreasingʳ _ _ ⟩
        𝟘ᶜ ∙ 𝟘 ∙ ⌜ m ⌝                              ∎)
     ▸B
     ok)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ ∧ᶜ γ             ≡˘⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

-- A usage lemma for sndᵣ with the mode set to 𝟘ᵐ.

sndᵣₘ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  Prodrec-restriction (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ 𝟘ᵐ ] t →
  δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  γ ▸[ 𝟘ᵐ ] sndᵣ p q A B t
sndᵣₘ-𝟘ᵐ {p = p} {q = q} {γ = γ} {δ = δ} ⦃ ok = 𝟘ᵐ-ok ⦄ ok B ▸t ▸B = sub
  (sndᵣₘ
     (inj₂ (inj₂ (λ ())))
     ok
     B
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸B) $ begin
        δ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (PE.cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
        δ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
        δ ∙ 𝟘            ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (▸-𝟘ᵐ ▸t) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)

-- A usage lemma for sndᵣ with the mode set to 𝟙ᵐ and the assumption
-- that 𝟘 is the largest quantity.

sndᵣₘ-𝟙ᵐ-≤𝟘 :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p → p ≤ 𝟘) →
  Prodrec-restriction (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ 𝟙ᵐ ] t →
  δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  γ ▸[ 𝟙ᵐ ] sndᵣ p q A B t
sndᵣₘ-𝟙ᵐ-≤𝟘 {γ = γ} 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘 ok B ▸t ▸B = sub
  (sndᵣₘ
     (case ≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘 of λ where
        (inj₁ 𝟘≰𝟙) → inj₁ 𝟘≰𝟙
        (inj₂ 𝟙≡𝟘) → inj₂ (inj₁ 𝟙≡𝟘))
     ok
     B
     ▸t
     ▸B)
  (begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (≤ᶜ𝟘ᶜ (≤𝟘 _)) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A usage lemma for sndᵣ with the mode set to 𝟙ᵐ and the assumption
-- that _+_ is pointwise bounded by _∧_.

sndᵣₘ-𝟙ᵐ-+≤∧ :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p q → p + q ≤ p ∧ q) →
  Prodrec-restriction (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ 𝟙ᵐ ] t →
  δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  γ ▸[ 𝟙ᵐ ] sndᵣ p q A B t
sndᵣₘ-𝟙ᵐ-+≤∧ 𝟙≡𝟘⊎𝟙≢𝟘 +≤∧ = sndᵣₘ-𝟙ᵐ-≤𝟘 𝟙≡𝟘⊎𝟙≢𝟘 (+≤∧→≤𝟘 +≤∧)

------------------------------------------------------------------------
-- Typing rules for sndᵣ

-- A typing rule for sndᵣ.

sndᵣⱼ :
  Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
  Γ ⊢ sndᵣ p q A B t ∷ B [ fstᵣ p A t ]
sndᵣⱼ {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t =   $⟨ prodrecⱼ ⊢A ⊢B (⊢[fstᵣ-0]↑ ⊢B ok) ⊢t
                                                                  (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok) ok ⟩
  Γ ⊢ sndᵣ p q A B t ∷ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]  →⟨ flip conv (⊢≡[fstᵣ] ⊢t) ⟩
  Γ ⊢ sndᵣ p q A B t ∷ B [ fstᵣ p A t ]                      □
  where
  ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
  ⊢A       = ⊢A,⊢B,ok .proj₁
  ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
  ok       = ⊢A,⊢B,ok .proj₂ .proj₂

-- A reduction rule for sndᵣ.

sndᵣ-β-⇒ :
  Γ ∙ A ⊢ B →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ] →
  Σᵣ-restriction p q →
  Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ⇒ u ∷ B [ fstᵣ p A (prodᵣ p t u) ]
sndᵣ-β-⇒
  {Γ = Γ} {A = A} {B = B} {t = t} {u = u} {p = p} {q = q} ⊢B ⊢t ⊢u ok =
                                                    $⟨ prodrec-β ⊢A ⊢B (⊢[fstᵣ-0]↑ {q = q} ⊢B ok) ⊢t ⊢u
                                                         (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok) PE.refl ok ⟩
  Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ⇒ u ∷
    B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p t u ]  →⟨ flip conv (⊢≡[fstᵣ] (prodⱼ {q = q} ⊢A ⊢B ⊢t ⊢u ok)) ⟩

  Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ⇒ u ∷
    B [ fstᵣ p A (prodᵣ p t u) ]                    □
  where
  ⊢A = syntacticTerm ⊢t

-- Another reduction rule for sndᵣ.

sndᵣ-subst :
  Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q ▷ A ▹ B →
  Γ ⊢ sndᵣ p q A B t₁ ⇒ sndᵣ p q A B t₂ ∷ B [ fstᵣ p A t₁ ]
sndᵣ-subst
  {Γ = Γ} {t₁ = t₁} {t₂ = t₂} {p = p} {q = q} {A = A} {B = B} t₁⇒t₂ =
                                           $⟨ prodrec-subst ⊢A ⊢B (⊢[fstᵣ-0]↑ ⊢B ok) (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok) t₁⇒t₂ ok ⟩
  Γ ⊢ sndᵣ p q A B t₁ ⇒ sndᵣ p q A B t₂ ∷
    B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t₁ ]  →⟨ flip conv (⊢≡[fstᵣ] ⊢t₁) ⟩

  Γ ⊢ sndᵣ p q A B t₁ ⇒ sndᵣ p q A B t₂ ∷
    B [ fstᵣ p A t₁ ]                      □
  where
  ⊢t₁      = syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₂ .proj₁
  ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t₁)
  ⊢A       = ⊢A,⊢B,ok .proj₁
  ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
  ok       = ⊢A,⊢B,ok .proj₂ .proj₂

-- An equality rule for sndᵣ.

sndᵣ-β-≡ :
  Γ ∙ A ⊢ B →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ] →
  Σᵣ-restriction p q →
  Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ≡ u ∷ B [ fstᵣ p A (prodᵣ p t u) ]
sndᵣ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (sndᵣ-β-⇒ ⊢B ⊢t ⊢u ok)

-- Another equality rule for sndᵣ.

sndᵣ-cong :
  Γ ⊢ A₁ ≡ A₂ →
  Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
  Γ ⊢ t₁ ≡ t₂ ∷ Σᵣ p , q ▷ A₁ ▹ B₁ →
  Γ ⊢ sndᵣ p q A₁ B₁ t₁ ≡ sndᵣ p q A₂ B₂ t₂ ∷ B₁ [ fstᵣ p A₁ t₁ ]
sndᵣ-cong
  {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} {t₁ = t₁} {t₂ = t₂}
  {p = p} {q = q} A₁≡A₂ B₁≡B₂ t₁≡t₂ =          $⟨ prodrec-cong ⊢A ⊢B (⊢[fstᵣ-0]↑≡[fstᵣ-0]↑ A₁≡A₂ B₁≡B₂ ok)
                                                    t₁≡t₂ (refl (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok)) ok ⟩
  Γ ⊢ sndᵣ p q A₁ B₁ t₁ ≡ sndᵣ p q A₂ B₂ t₂ ∷
    B₁ [ fstᵣ p (wk1 A₁) (var x0) ]↑ [ t₁ ]    →⟨ flip conv (⊢≡[fstᵣ] ⊢t₁) ⟩

  Γ ⊢ sndᵣ p q A₁ B₁ t₁ ≡ sndᵣ p q A₂ B₂ t₂ ∷
    B₁ [ fstᵣ p A₁ t₁ ]                        □
  where
  ⊢t₁      = syntacticEqTerm t₁≡t₂ .proj₂ .proj₁
  ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t₁)
  ⊢A       = ⊢A,⊢B,ok .proj₁
  ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
  ok       = ⊢A,⊢B,ok .proj₂ .proj₂

-- Presumably it is possible to prove that the following η-rule does
-- not hold in general:
--
--   Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
--   Γ ⊢ u ∷ Σᵣ p , q ▷ A ▹ B →
--   Γ ⊢ fstᵣ p A t ≡ fstᵣ p A u ∷ A →
--   Γ ⊢ sndᵣ p q A B t ≡ sndᵣ p q A B u ∷ B [ fstᵣ p A t ] →
--   Γ ⊢ t ≡ u ∷ Σᵣ p , q ▷ A ▹ B
