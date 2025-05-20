------------------------------------------------------------------------
-- Counterexample to resource correctness when some assumptions are
-- dropped.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Heap.Assumptions
open import Definition.Typed.Restrictions

module Graded.Heap.Soundness.Counterexample
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
open import Tools.Nat using (1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Reasoning.PropositionalEquality

open import Definition.Untyped M
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.Substitution TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Reduction
  type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Inversion type-variant UR factoring-nr

private variable
  Δ : Con Term _
  t : Term _
  γ : Conₘ _
  p q : M

opaque

  -- A counterexample to the resource correctness theorem for inconsistent contexts.
  -- Note that several of the conclusions of that theorem are invalidated
  --
  -- There is a term that evaluates to a final state but:
  --   1. It does not evaluate to a numeral
  --   2. The stack of the final state is not empty
  --   3. If p ≰ 𝟘 for some p then the grades of the entries of the final heap
  --      are not bounded by 𝟘.

  ¬soundness-inconsistent :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    Π-allowed p 𝟘 →
    ∃₃ λ l (Δ : Con Term l) t →
    ¬ Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ∃₆ λ m n H u (ρ : Wk m n) S →
    initial t ↠* ⟨ H , u , ρ , S ⟩ ×
    (∀ {m′ n′} (s : State _ m′ n′) → ⟨ H , u , ρ , S ⟩ ↠ s → ⊥) ×
    S PE.≢ ε ×
    ¬ (∃ λ k → u PE.≡ sucᵏ k) ×
    ((p ≤ 𝟘 → ⊥) → ¬ H ≤ʰ 𝟘)
  ¬soundness-inconsistent {p} ok₁ ok₂ =
    let Δ = ε ∙ Empty
        ⊢Δ = ∙ Emptyⱼ ε
        ⊢Δ′ = ∙ ℕⱼ ⊢Δ
        ⊢ℕ = ℕⱼ ⊢Δ′
        H = erasedHeap 1 ∙ (𝟙 · p , zero , id)
        S = emptyrecₑ 𝟘 (Π p , 𝟘 ▷ ℕ ▹ ℕ) (lift id) ∙ (∘ₑ p (var y0) (lift id) ∙ ε)
        t = lam p (emptyrec 𝟘 (Π p , 𝟘 ▷ ℕ ▹ ℕ) (var x1) ∘⟨ p ⟩ var x0) ∘⟨ p ⟩ zero
        ⊢t = lamⱼ ⊢ℕ (emptyrecⱼ (ΠΣⱼ (ℕⱼ (∙ ℕⱼ ⊢Δ′)) ok₂) (var ⊢Δ′ (there here)) ∘ⱼ var ⊢Δ′ here) ok₂ ∘ⱼ zeroⱼ ⊢Δ
        eq₁ = begin
          𝟙 · p                 ≡⟨ ·-identityˡ _ ⟩
          p                     ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + p                 ≡˘⟨ +-cong (·-zeroˡ _) ·⌜⌞⌟⌝ ⟩
          𝟘 · 𝟘 + p · ⌜ ⌞ p ⌟ ⌝ ∎
        eq₃ = begin
          𝟘         ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟘     ≡˘⟨ +-congˡ (·-zeroʳ _) ⟩
          𝟘 + p · 𝟘 ∎
        eq₂ = begin
          𝟘                      ≡⟨ eq₃ ⟩
          𝟘 + p · 𝟘              ≡˘⟨ +-congʳ (·-zeroˡ _) ⟩
          𝟘 ·  ⌜ ⌞ 𝟘 ⌟ ⌝ + p · 𝟘 ∎
        ▸t = sub (lamₘ (sub (emptyrecₘ var (ΠΣₘ {δ = 𝟘ᶜ} ℕₘ (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _)))) ok₁ ∘ₘ var)
                         (≤ᶜ-reflexive (ε ∙ eq₂ ∙ eq₁))) ∘ₘ zeroₘ)
              (≤ᶜ-reflexive (ε ∙ eq₃))
    in  _ , Δ , t , (λ consistent → consistent (var x0) (var ⊢Δ here)) , ⊢t , ▸t
          , _ , _ , H , var x1 , lift id , S
          , (⇾ₑ (⇒ₑ appₕ) ⇨ ⇒ᵥ (lamₕ ε) ⇨ ⇾ₑ (⇒ₑ appₕ) ⇨  ⇾ₑ (⇒ₑ emptyrecₕ) ⇨ id)
          , (λ { s (⇾ₑ d) → ¬↦∧↦● (↦[]→↦ (⇾ₑ-inv-var d .proj₂ .proj₂ .proj₂)) (there here)
               ; s (⇒ᵥ d) → ⇒ᵥ-inv-var d
               ; s (⇒ₙ d) → ⇒ₙ-inv-var d})
          , (λ ())
          , (λ { (0 , ()) ; (1+ _ , ())})
          , λ { p≰𝟘 (_ ∙ p≤𝟘) → p≰𝟘 (PE.subst (_≤ 𝟘) (·-identityˡ _) p≤𝟘) }

opaque

  -- A counterexample to the resource correctness theorem with erased matches for unitrec.
  -- Note that several of the conclusions of that theorem are invalidated
  --
  -- There is a term that evaluates to a final state but:
  --   1. It does not evaluate to a numeral
  --   2. The stack of the final state is not empty
  --   3. If 𝟙 ≰ 𝟘 then the grades of the entries of the final heap are not bounded by 𝟘.

  ¬soundness-erased-matches-unitrec :
    Unitʷ-allowed →
    Π-allowed 𝟙 𝟘 →
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    ¬ Unitʷ-η →
    ∃₃ λ l (Δ : Con Term l) t →
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ∃₆ λ m n H u (ρ : Wk m n) S →
    initial t ↠* ⟨ H , u , ρ , S ⟩ ×
    (∀ {m′ n′} (s : State _ m′ n′) → ⟨ H , u , ρ , S ⟩ ↠ s → ⊥) ×
    S PE.≢ ε ×
    ¬ (∃ λ k → u PE.≡ sucᵏ k) ×
    ((𝟙 ≤ 𝟘 → ⊥) → ¬ H ≤ʰ 𝟘)
  ¬soundness-erased-matches-unitrec ok₁ ok₂ ok₃ no-η =
    let Δ = ε ∙ Unitʷ 0
        ⊢Δ = ∙ Unitⱼ ε ok₁
        ⊢Δ′ = ∙ ℕⱼ ⊢Δ
        H = erasedHeap 1 ∙ (𝟙 · 𝟙 , zero , id)
        S = unitrecₑ 0 𝟘 𝟘 ℕ (var x0) (lift id) ∙ ε
        t = lam 𝟙 (unitrec 0 𝟘 𝟘 ℕ (var x1) (var x0)) ∘⟨ 𝟙 ⟩ zero
        ⊢t = lamⱼ (ℕⱼ ⊢Δ′)
               (unitrecⱼ (ℕⱼ (∙ Unitⱼ ⊢Δ′ ok₁)) (var ⊢Δ′ (there here)) (var ⊢Δ′ here) ok₁) ok₂
              ∘ⱼ zeroⱼ ⊢Δ
        eq₁ = begin
          𝟙 · 𝟙     ≡⟨ ·-identityˡ _ ⟩
          𝟙         ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟙     ≡˘⟨ +-congʳ (·-zeroˡ _) ⟩
          𝟘 · 𝟘 + 𝟙 ∎
        eq₃ = begin
          𝟘         ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟘     ≡˘⟨ +-congˡ (·-zeroʳ _) ⟩
          𝟘 + 𝟙 · 𝟘 ∎
        eq₂ = begin
          𝟘                  ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟘              ≡˘⟨ +-congʳ (·-zeroˡ _) ⟩
          𝟘 ·  ⌜ ⌞ 𝟘 ⌟ ⌝ + 𝟘 ∎
        ▸t = sub (lamₘ (sub (unitrecₘ {η = 𝟘ᶜ} var var (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _))) ok₃)
                               (≤ᶜ-reflexive (ε ∙ eq₂ ∙ eq₁))) ∘ₘ zeroₘ)
              (≤ᶜ-reflexive (ε ∙ eq₃))
    in  _ , Δ , t , (λ _ x → ¬Empty (substTerm x (starⱼ ε ok₁))) , ⊢t , ▸t
          , _ , _ , H , var x1 , lift id , S
          , (⇾ₑ (⇒ₑ appₕ) ⇨ ⇒ᵥ (lamₕ ε) ⇨ ⇾ₑ (⇒ₑ unitrecₕ no-η) ⇨ id)
          , (λ { s (⇾ₑ d) → ¬↦∧↦● (↦[]→↦ (⇾ₑ-inv-var d .proj₂ .proj₂ .proj₂)) (there here)
               ; s (⇒ᵥ d) → ⇒ᵥ-inv-var d
               ; s (⇒ₙ d) → ⇒ₙ-inv-var d})
          , (λ ())
          , (λ { (0 , ()) ; (1+ _ , ())})
          , λ { 𝟙≰𝟘 (_ ∙ 𝟙≤𝟘) → 𝟙≰𝟘 (PE.subst (_≤ 𝟘) (·-identityˡ _) 𝟙≤𝟘) }

opaque

  -- A counterexample to the resource correctness theorem with erased matches for prodrec.
  -- Note that several of the conclusions of that theorem are invalidated
  --
  -- There is a term that evaluates to a final state but:
  --   1. It does not evaluate to a numeral
  --   2. The stack of the final state is not empty
  --   3. If 𝟙 ≰ 𝟘 then the grades of the entries of the final heap are not bounded by 𝟘.

  ¬soundness-erased-matches-prodrec :
    Σʷ-allowed p 𝟘 →
    Π-allowed 𝟙 𝟘 →
    Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 →
    ∃₃ λ l (Δ : Con Term l) t →
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ∃₆ λ m n H u (ρ : Wk m n) S →
    initial t ↠* ⟨ H , u , ρ , S ⟩ ×
    (∀ {m′ n′} (s : State _ m′ n′) → ⟨ H , u , ρ , S ⟩ ↠ s → ⊥) ×
    S PE.≢ ε ×
    ¬ (∃ λ k → u PE.≡ sucᵏ k) ×
    ((𝟙 ≤ 𝟘 → ⊥) → ¬ H ≤ʰ 𝟘)
  ¬soundness-erased-matches-prodrec {p} ok₁ ok₂ ok₃ =
    let Δ = ε ∙ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ
        ⊢Δ = ∙ ΠΣⱼ (ℕⱼ (∙ ℕⱼ ε)) ok₁
        ⊢Δ′ = ∙ ℕⱼ ⊢Δ
        ⊢Δ″ = ∙ ℕⱼ ⊢Δ′
        H = erasedHeap 1 ∙ (𝟙 · 𝟙 , zero , id)
        S = prodrecₑ 𝟘 p 𝟘 ℕ (var x2) (lift id) ∙ ε
        t = lam 𝟙 (prodrec 𝟘 p 𝟘 ℕ (var x1) (var x2)) ∘⟨ 𝟙 ⟩ zero
        ⊢t = lamⱼ (ℕⱼ ⊢Δ′)
                    (prodrecⱼ (ℕⱼ (∙ ΠΣⱼ (ℕⱼ ⊢Δ″) ok₁)) (var ⊢Δ′ (there here)) (var (∙ ℕⱼ ⊢Δ″) (there (there here))) ok₁) ok₂
                  ∘ⱼ zeroⱼ ⊢Δ
        eq₁ = begin
          𝟙 · 𝟘 · p ≡⟨ ·-identityˡ _ ⟩
          𝟘 · p     ≡⟨ ·-zeroˡ _ ⟩
          𝟘         ∎
        eq₂ = begin
          𝟙 · 𝟙     ≡⟨ ·-identityˡ _ ⟩
          𝟙         ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟙     ≡˘⟨ +-congʳ (·-zeroʳ _) ⟩
          𝟘 · 𝟘 + 𝟙 ∎
        eq₃ = begin
          𝟘                            ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟘                        ≡˘⟨ +-cong (+-identityˡ _) (·-identityˡ _) ⟩
          (𝟘 + 𝟘) + 𝟙 · 𝟘              ≡˘⟨ +-congʳ (+-congʳ (·-zeroˡ _)) ⟩
          (𝟘 ·  ⌜ ⌞ 𝟘 ⌟ ⌝ + 𝟘) + 𝟙 · 𝟘 ∎
        ▸t = sub (lamₘ (sub (prodrecₘ {η = 𝟘ᶜ} var (sub var (≤ᶜ-reflexive (≈ᶜ-refl ∙ eq₁ ∙ ·-zeroʳ _)))
                              (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _))) ok₃)
                            (≤ᶜ-reflexive (≈ᶜ-refl ∙ eq₂)))
                 ∘ₘ zeroₘ)
                 (ε ∙ ≤-reflexive eq₃)
    in  _ , Δ , t , (λ _ x → ¬Empty (substTerm x (prodⱼ (ℕⱼ (∙ ℕⱼ ε)) (zeroⱼ ε) (zeroⱼ ε) ok₁))) , ⊢t , ▸t
          , _ , _ , H , var x1 , lift id , S
          , (⇾ₑ (⇒ₑ appₕ) ⇨ ⇒ᵥ (lamₕ ε) ⇨ ⇾ₑ (⇒ₑ prodrecₕ) ⇨ id)
          , (λ { s (⇾ₑ d) → ¬↦∧↦● (↦[]→↦ (⇾ₑ-inv-var d .proj₂ .proj₂ .proj₂)) (there here)
               ; s (⇒ᵥ d) → ⇒ᵥ-inv-var d
               ; s (⇒ₙ d) → ⇒ₙ-inv-var d})
          , (λ ())
          , (λ { (0 , ()) ; (1+ _ , ())})
          , λ { 𝟙≰𝟘 (_ ∙ 𝟙≤𝟘) → 𝟙≰𝟘 (PE.subst (_≤ 𝟘) (·-identityˡ _) 𝟙≤𝟘) }

opaque

  -- A counterexample to the resource correctness theorem for programs that use free
  -- variables in a non-erased way.
  -- Note that several of the conclusions of that theorem are invalidated
  --
  -- There is a term that evaluates to a final state but:
  --   1. It does not evaluate to a numeral
  --   2. The stack of the final state is not empty
  --   3. If 𝟙 ≰ 𝟘 then the grades of the entries of the final heap are not bounded by 𝟘.

  ¬soundness-not-erased :
    Π-allowed 𝟙 𝟘 →
    ∃₄ λ l (Δ : Con Term l) γ t →
    Consistent Δ ×
    γ ≈ᶜ 𝟙ᶜ ×
    Δ ⊢ t ∷ ℕ ×
    γ ▸[ 𝟙ᵐ ] t ×
    ∃₆ λ m n H u (ρ : Wk m n) S →
    initial t ↠* ⟨ H , u , ρ , S ⟩ ×
    (∀ {m′ n′} (s : State _ m′ n′) → ⟨ H , u , ρ , S ⟩ ↠ s → ⊥) ×
    S PE.≢ ε ×
    ¬ (∃ λ k → u PE.≡ sucᵏ k) ×
    ((𝟙 ≤ 𝟘 → ⊥) → ¬ H ≤ʰ 𝟘)
  ¬soundness-not-erased ok =
    let Δ = ε ∙ Π 𝟙 , 𝟘 ▷ ℕ ▹ ℕ
        ⊢Δ = ∙ ΠΣⱼ (ℕⱼ (∙ ℕⱼ ε)) ok
        ⊢Δ′ = ∙ ℕⱼ ⊢Δ
        H = erasedHeap 1 ∙ (𝟙 · 𝟙 , zero , id)
        S = ∘ₑ 𝟙 (var y0) (lift id) ∙ ε
        t = lam 𝟙 (var x1 ∘⟨ 𝟙 ⟩ var x0) ∘⟨ 𝟙 ⟩ zero
        ⊢t = lamⱼ (ℕⱼ ⊢Δ′) (var ⊢Δ′ (there here) ∘ⱼ var ⊢Δ′ here) ok ∘ⱼ zeroⱼ ⊢Δ
        eq₁ = begin
          𝟙         ≡˘⟨ +-identityʳ _ ⟩
          𝟙 + 𝟘     ≡˘⟨ +-congˡ (·-zeroʳ _) ⟩
          𝟙 + 𝟙 · 𝟘 ∎
        eq₂ = begin
          𝟙 · 𝟙             ≡˘⟨ +-identityˡ _ ⟩
          𝟘 + 𝟙 · 𝟙         ≡˘⟨ +-congˡ (·-congˡ (PE.cong ⌜_⌝ ⌞𝟙⌟)) ⟩
          𝟘 + 𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝ ∎
        ▸t = sub (lamₘ (sub (var ∘ₘ var) (≤ᶜ-reflexive (ε ∙ eq₁ ∙ eq₂)))
                  ∘ₘ zeroₘ)
               (ε ∙ ≤-reflexive eq₁)
    in  _ , Δ , _ , t , (λ _ x → ¬Empty (substTerm x (lamⱼ (ℕⱼ (∙ ℕⱼ ε)) (var (∙ ℕⱼ ε) here) ok)))
          , ≈ᶜ-refl , ⊢t , ▸t
          , _ , _ , H , var x1 , lift id , S
          , (⇾ₑ (⇒ₑ appₕ) ⇨ ⇒ᵥ (lamₕ ε) ⇨ ⇾ₑ (⇒ₑ appₕ) ⇨ id)
          , (λ { s (⇾ₑ d) → ¬↦∧↦● (↦[]→↦ (⇾ₑ-inv-var d .proj₂ .proj₂ .proj₂)) (there here)
               ; s (⇒ᵥ d) → ⇒ᵥ-inv-var d
               ; s (⇒ₙ d) → ⇒ₙ-inv-var d})
          , (λ ())
          , (λ { (0 , ()) ; (1+ _ , ())})
          , λ { 𝟙≰𝟘 (_ ∙ 𝟙≤𝟘) → 𝟙≰𝟘 (PE.subst (_≤ 𝟘) (·-identityˡ _) 𝟙≤𝟘) }
