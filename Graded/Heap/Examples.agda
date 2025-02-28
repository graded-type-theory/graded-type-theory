------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Heap.Assumptions
open import Definition.Typed.Restrictions

module Graded.Heap.Examples
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (As : Assumptions UR TR)
  where

open Modality 𝕄
open Type-restrictions TR
open Assumptions As

open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality as PE

open import Graded.Context 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Inversion type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr
open import Graded.Heap.Soundness UR TR As

open import Definition.Untyped M
open import Definition.Untyped.Sigma 𝕄 hiding (fstʷ)
open import Definition.Typed TR

private variable
  k n : Nat
  t t′ : Term _
  γ : Conₘ _
  m : Mode
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  S S′ : Stack _

-- First projection for weak Σ-types, specialized to pairs of natural
-- numbers with grade 𝟙 for the first component.

fstʷ : Term n → Term n
fstʷ = Fstʷ-sndʷ.fstʷ 𝟙 𝟘 𝟙 ℕ

opaque

  -- Evaluating fstʷ (prodʷ 𝟙 zero zero) in the heap yields the state
  -- ⟨ ε ∙ (𝟙 , zero , id) ∙ (𝟙 , zero , step id) , var x1 , stepn id 2 , ε ⟩

  fstʷ⟨0,0⟩↠*′ :
    initial {k = 0} (fstʷ (prodʷ 𝟙 zero zero)) ↠*
    ⟨ ε ∙ (𝟙 , zero , id) ∙ (𝟙 , zero , step id) , var x1 , liftn id 2 , ε ⟩
  fstʷ⟨0,0⟩↠*′ =
    ⇾ₑ (⇒ₑ prodrecₕ) ⇨
    ⇒ᵥ prodʷₕ ε ⇨
    subst₂ (λ p q → ⟨ ε ∙ (p , zero , id) ∙ (q , zero , step id) , _ , _ , _ ⟩ ↠*
                 ⟨ ε ∙ (𝟙 , zero , id) ∙ (𝟙 , zero , step id) , _ , _ , _ ⟩)
      (PE.sym (PE.trans (·-identityˡ _) (·-identityʳ _))) (PE.sym (·-identityʳ _)) id

opaque

  -- Evaluating fstʷ (prodʷ 𝟙 zero zero) in the heap yields the state
  -- ⟨ ε ∙ (𝟘 , zero , id) ∙ (𝟙 , zero , step id) , zero , stepn id 2 , ε ⟩
  -- if 𝟙 - 𝟙 ≡ 𝟘.

  fstʷ⟨0,0⟩↠* :
    𝟙 - 𝟙 ≡ 𝟘 →
    initial {k = 0} (fstʷ (prodʷ 𝟙 zero zero)) ↠*
    ⟨ ε ∙ (𝟘 , zero , id) ∙ (𝟙 , zero , step id) , zero , stepn id 2 , ε ⟩
  fstʷ⟨0,0⟩↠* 𝟙-𝟙≡𝟘 =
    ⇾ₑ (⇒ₑ prodrecₕ) ⇨
    ⇒ᵥ prodʷₕ ε ⇨
    ⇾ₑ var ε (there (here (subst (_- 𝟙 ≡ 𝟘)
         (PE.sym (PE.trans (·-identityˡ _) (·-identityˡ _))) 𝟙-𝟙≡𝟘))) ⇨
    subst (λ p → ⟨ ε ∙ (𝟘 , zero , id) ∙ (p , zero , step id) , _ , _ , _ ⟩ ↠*
                 ⟨ ε ∙ (𝟘 , zero , id) ∙ (𝟙 , zero , step id) , _ , _ , _ ⟩)
      (PE.sym (·-identityʳ 𝟙)) id

opaque

  -- If fstʷ has a usage rule then 𝟙 ≤ 𝟘 (given some assumptions).

  fstʷ-has-usage→𝟙≤𝟘 :
    Σʷ-allowed 𝟙 𝟘 →
    𝟙 - 𝟙 ≡ 𝟘 →
    (∀ {n} {γ : Conₘ n} {t m} → γ ▸[ m ] t →
      ∃ λ δ → δ ▸[ m ] fstʷ t) →
    𝟙 ≤ 𝟘
  fstʷ-has-usage→𝟙≤𝟘 ok 𝟙-𝟙≡𝟘 ▸fstʷ =
    let s = initial {k = 0} (fstʷ (prodʷ 𝟙 zero zero))
        ⊢ℕ = ℕⱼ (∙ ℕⱼ ε)
        ⊢s = prodrecⱼ (ℕⱼ (∙ ΠΣⱼ ⊢ℕ ok))
              (prodⱼ ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) ok)
              (var (∙ ⊢ℕ) (there here)) ok
        ▸s = sub (▸fstʷ (prodʷₘ zeroₘ zeroₘ) .proj₂) (ε≤ _)
        _ , _ , H , _ , _ , d , _ , H≤𝟘 = soundness-closed ⊢s ▸s
        m≡ , n≡ , s≡ = ↠*-det d (fstʷ⟨0,0⟩↠* 𝟙-𝟙≡𝟘)
                        (λ _ → ↠-inv-sucᵏ) (λ _ → ↠-inv-sucᵏ)
    in  lemma m≡ n≡ s≡ H≤𝟘
    where
    ε≤ : ∀ δ → ε ≤ᶜ δ
    ε≤ ε = ε
    lemma :
      (x : k ≡ 2) (y : n ≡ 0) →
      subst₂ (State 0) x y (⟨ H , t , ρ , S ⟩) ≡
        ⟨ ε ∙ (𝟘 , zero , id) ∙ (𝟙 , zero , step id) , t′ , ρ′ , S′ ⟩ →
      H ≤ʰ 𝟘 → 𝟙 ≤ 𝟘
    lemma refl refl refl (H≤ ∙ 𝟙≤𝟘) = 𝟙≤𝟘
