------------------------------------------------------------------------
-- Examples related to non-interference for the abstract machine
------------------------------------------------------------------------

open import Graded.Modality
import Graded.Mode.Instances.Bounded-distributive-lattice
open import Graded.Usage.Restrictions
open import Graded.Heap.Assumptions
import Graded.Modality.Instances.Bounded-distributive-lattice
open import Definition.Typed.Restrictions
import Tools.PropositionalEquality as PE
open import Tools.Algebra
open import Tools.Relation

module Graded.Heap.Non-interference.Examples
  {a} {M : Set a}
  (L : Bounded-distributive-lattice M)
  (open Bounded-distributive-lattice L using (⊤; ⊥; ⊥≤; ≤⊤))
  (is-⊤? : ∀ p → Dec (p PE.≡ ⊤))
  (open Graded.Modality.Instances.Bounded-distributive-lattice M L is-⊤?)
  (open Graded.Mode.Instances.Bounded-distributive-lattice L is-⊤?)
  (UR : Usage-restrictions modality bounded-distributive-lattice-isMode)
  (TR : Type-restrictions modality)
  -- The security level programs should be run in
  (ℓ₀ : M)
  (As : Assumptions UR TR ℓ₀)
  (open Usage-restrictions UR)
  ⦃ no-nr : Nr-not-available-GLB ⦄
  where

open Type-restrictions TR
open Assumptions As
open Modality modality

open import Graded.Heap.Non-interference L is-⊤? UR TR ℓ₀ As
open import Graded.Heap.Reduction type-variant UR factoring-nr ℓ₀
import Graded.Heap.Reduction.Reasoning type-variant UR factoring-nr ℓ₀ as R
open import Graded.Heap.Termination UR TR ℓ₀ As
open import Graded.Heap.Typed UR TR factoring-nr ℓ₀
open import Graded.Heap.Untyped type-variant UR factoring-nr ℓ₀
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ℓ₀
open import Graded.Heap.Usage type-variant UR factoring-nr ℓ₀

open import Graded.Context modality hiding (_⟨_⟩)
open import Graded.Context.Properties modality
open import Graded.Derived.Nat UR
open import Graded.Modality.Properties modality
open import Graded.Usage UR
open import Graded.Usage.Inversion UR

open import Definition.Untyped M
open import Definition.Untyped.Nat modality
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed TR
open import Definition.Typed.Properties TR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  m n : Nat
  u v : Term _
  p q : M
  ρ : Wk _ _
  γ : Conₘ _

private opaque

  -- A lemma used below. If ℓ₀ is not equal to 𝟘 then it is not at least
  -- as secret as 𝟘.

  𝟘≰ℓ₀ : ℓ₀ ≢ 𝟘 → ¬ 𝟘 ≤ ℓ₀
  𝟘≰ℓ₀ ℓ₀≢𝟘 =
    ℓ₀≢𝟘 ∘→ ≤-antisym (≤⊤ _)

------------------------------------------------------------------------
-- The assumption that there are no secret matches is not necessary.
-- That is, there are programs with secret matches that are
-- non-interferent.

opaque

  non-interference-with-secret-matches :
    -- We do not have access to secret information
    -- as otherwise there are no secret matches.
    (ℓ₀≢𝟘 : ℓ₀ ≢ 𝟘)
    -- Secret matches on weak pairs is allowed
    (prodrec-ok : Prodrec-allowed ℓ₀ 𝟘 𝟘 𝟘)
    -- A certain Σ-type is allowed
    (Σ-ok : Σʷ-allowed 𝟘 𝟘) →
    ∃₄ λ k (t : Term k) γ Γ →
    ¬ No-secret-matches ×
    γ ▸[ ℓ₀ ] t ×
    ε » Γ ⊢ t ∷ ℕ ×
    ∀ H₁ H₂ → H₁ ~⟨ ℓ₀ ⟩ H₂ → ε ⊢ʰ H₁ ∷ Γ → γ ▸ʰ H₁ →
    ∃₆ λ m n H₁′ H₂′ (ρ : Wk m n) u →
       ⟨ H₁ , t , id , ε ⟩ ↠* ⟨ H₁′ , u , ρ , ε ⟩ ×
       ⟨ H₂ , t , id , ε ⟩ ↠* ⟨ H₂′ , u , ρ , ε ⟩ ×
       Numeral u × H₁′ ~⟨ ℓ₀ ⟩ H₂′
  non-interference-with-secret-matches ℓ₀≢𝟘 prodrec-ok Σ-ok =
    _ , t , ε , ε , secret-matches , ▸t , ⊢t
      , λ H₁ H₂ H₁~H₂ ⊢H₁ ▸H₁ →
       _ , _ , _ , _ , _ , _ , ⟨t⟩⇒⟨zero⟩ H₁ , ⟨t⟩⇒⟨zero⟩ H₂ , zeroₙ
         , (H₁~H₂ ∙ (⊥-elim ∘→ 𝟘≰ℓ₀ ℓ₀≢𝟘) ∙ (⊥-elim ∘→ 𝟘≰ℓ₀ ℓ₀≢𝟘))
    where

    -- The program t corresponds to
    -- let (_ , _) = (zero , zero) in zero
    t : Term 0
    t = prodrec 𝟘 𝟘 𝟘 ℕ (prodʷ 𝟘 zero zero) zero

    -- There are no secret matches

    secret-matches : ¬ No-secret-matches
    secret-matches nsm =
      𝟘≰ℓ₀ ℓ₀≢𝟘 (No-secret-matches.no-secret-prodrec nsm ≤-refl prodrec-ok)

    -- The program t is well-resourced.

    ▸t : ε ▸[ ℓ₀ ] t
    ▸t =
      let ▸zero = sub-≈ᶜ zeroₘ $ begin
            𝟘ᶜ ∙ ℓ₀ · 𝟘 · 𝟘 ∙ ℓ₀ · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-zeroʳ _) ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ ∙ ℓ₀ · 𝟘 ∙ 𝟘          ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ refl ⟩
            𝟘ᶜ ∙ 𝟘 ∙ 𝟘               ≡⟨⟩
            𝟘ᶜ                       ∎
          ▸ℕ = sub-≈ᶜ ℕₘ $ begin
            𝟘ᶜ ∙ 𝟘 · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ ∙ 𝟘     ≡⟨⟩
            𝟘ᶜ         ∎
      in  prodrecₘ (prodʷₘ zeroₘ zeroₘ) ▸zero ▸ℕ prodrec-ok
      where
      open ≈ᶜ-reasoning

    -- The program t is well-typed (of type ℕ).

    ⊢t : ε » ε ⊢ t ∷ ℕ
    ⊢t =
      let ⊢ℕ = ℕⱼ (∙ ℕⱼ εε)
      in  prodrecⱼ (ℕⱼ (∙ (ΠΣⱼ ⊢ℕ Σ-ok)))
            (prodⱼ ⊢ℕ (zeroⱼ εε) (zeroⱼ εε) Σ-ok)
            (zeroⱼ (∙ ⊢ℕ)) Σ-ok

    -- The program t evaluates to zero in the abstract machine (and the
    -- heap is extended in a certain way).

    ⟨t⟩⇒⟨zero⟩ :
      ∀ (H : Heap 0 0) →
      ⟨ H , t , id , ε ⟩ ↠*
      ⟨ H ∙ (𝟘 , zero , id) ∙ (𝟘 , zero , step id) , zero , liftn id 2 , ε ⟩
    ⟨t⟩⇒⟨zero⟩ H =
      let u = prodʷ 𝟘 zero zero
          H′ = H ∙ (ℓ₀ · 𝟘 · 𝟘 , zero , id) ∙ (ℓ₀ · 𝟘 , zero , step id)
          H″ = H ∙ (𝟘 , zero , id) ∙ (𝟘 , zero , step id)
          H′≡H″ = cong₂ (λ x y → (H ∙ (x , _)) ∙ (y , _))
                    (PE.trans (·-congˡ (·-zeroʳ _)) (·-zeroʳ _))
                    (·-zeroʳ _)
          open R
      in
        ⟨ H , t                      , id         , ε ⟩                            ≡⟨⟩↠
        ⟨ H , prodrec 𝟘 𝟘 𝟘 ℕ u zero , id         , ε ⟩                            ⇒ₑ⟨ prodrecₕ ⟩
        ⟨ H , prodʷ 𝟘 zero zero      , id         , prodrecₑ 𝟘 𝟘 𝟘 ℕ zero id ∙ ε ⟩ ⇒ᵥ⟨ prodʷₕ ε ⟩
        ⟨ H′ , zero                  , liftn id 2 , ε ⟩                            ≡⟨ H′≡H″ ⨾ refl ⨾ refl ⨾ refl ⟩↠
        ⟨ H″ , zero                  , liftn id 2 , ε ⟩                            ∎

opaque
  unfolding natcase

  -- There are programs that are not well-resourced, but still are
  -- non-interferent.

  non-interference-with-not-well-resourced :
    -- ℓ₀ is not 𝟘
    (ℓ₀≢𝟘 : ℓ₀ ≢ 𝟘) →
    -- Certain Π-types are allowed
    Π-allowed 𝟘 𝟘 →
    ∃₃ λ k (t : Term k) Γ →
    (∀ γ → ¬ γ ▸[ ℓ₀ ] t) ×
    ε » Γ ⊢ t ∷ ℕ ×
    ∀ {γ : Conₘ k} H₁ H₂ →
      γ ▸ʰ H₁ → ε ⊢ʰ H₁ ∷ Γ →
      H₁ ~⟨ ℓ₀ ⟩ H₂ →
      ∃₆ λ m n H₁′ H₂′ (ρ : Wk m n) u →
      ⟨ H₁ , t , id , ε ⟩ ↠* ⟨ H₁′ , u , ρ , ε ⟩ ×
      ⟨ H₂ , t , id , ε ⟩ ↠* ⟨ H₂′ , u , ρ , ε ⟩ ×
      Numeral u × H₁′ ~⟨ ℓ₀ ⟩ H₂′
  non-interference-with-not-well-resourced ℓ₀≢𝟘 Π-ok =
    _ , t , _ , ¬▸t , ⊢t , λ H₁ H₂ ▸H₁ ⊢H₁ H₁~H₂ →
        _ , _ , _ , _ , _ , _ , ⟨t⟩⇒⟨zero⟩ H₁ , ⟨t⟩⇒⟨zero⟩ H₂
      , zeroₙ , (H₁~H₂ ∙ (λ _ → refl) ∙ (λ _ → refl) ∙ λ _ → refl)

    where

    -- The program t more or less corresponds to the following (x is secret):
    -- if (1 + x == zero)
    --   then 1
    --   else 0

    t : Term 1
    t = lam 𝟘 (natcase 𝟘 𝟘 ℕ (suc zero) zero (suc (var x0))) ∘⟨ 𝟘 ⟩ var x0

    -- The program t is well-typed (of type ℕ).

    ⊢t : ε » (ε ∙ ℕ) ⊢ t ∷ ℕ
    ⊢t =
      let ⊢ℕ = ℕⱼ εε
          ⊢ℕ′ = ℕⱼ (∙ ⊢ℕ)
          ⊢ℕ″ = ℕⱼ (∙ ⊢ℕ′)
      in  lamⱼ ⊢ℕ″
            (⊢natcase (ℕⱼ (∙ ⊢ℕ″)) (sucⱼ (zeroⱼ (∙ ⊢ℕ′))) (zeroⱼ (∙ ⊢ℕ″)) (sucⱼ (var (∙ ⊢ℕ′) here))) Π-ok ∘ⱼ
          var (∙ ⊢ℕ) here

    -- The program t is not well-resourced under any context.

    ¬▸t : ∀ γ → ¬ γ ▸[ ℓ₀ ] t
    ¬▸t (_ ∙ p) ▸t =
      case inv-usage-app ▸t of λ {
        (invUsageApp  ▸λ ▸x0 _) →
      case inv-usage-lam ▸λ of λ {
        (invUsageLam ▸nc _) →
      case inv-usage-natcase-glb ▸nc of λ {
        (_ ∙ _ ∙ p₁ , _ ∙ _ ∙ p₂ , _ ∙ _ ∙ p₃ , _ , ▸1 , ▸0 , ▸sucx , _ , _ ∙ _ ∙ 𝟘≤) →
      case inv-usage-numeral ▸1 (sucₙ zeroₙ) of λ {
        (_ ∙ _ ∙ p₁≤) →
      case inv-usage-numeral ▸0 zeroₙ of λ {
        (_ ∙ _ ∙ p₂≤ ∙ _) →
      case inv-usage-suc ▸sucx of λ {
        (invUsageSuc {δ = _ ∙ p₄} ▸x (_ ∙ p₃≤)) →
      𝟘≰ℓ₀ ℓ₀≢𝟘 $ begin
        𝟘                      ≈˘⟨ ·-zeroʳ _ ⟩
        ℓ₀ · 𝟘                 ≤⟨ 𝟘≤ ⟩
        (𝟙 ∧ 𝟘) · p₃ + p₁ ∧ p₂ ≤⟨ +-monotone (·-monotoneˡ (∧-decreasingˡ _ _)) (∧-monotone p₁≤ p₂≤) ⟩
        𝟙 · p₃ + 𝟘 ∧ 𝟘         ≈⟨ +-cong (·-identityˡ _) (∧-idem _) ⟩
        p₃ + 𝟘                 ≈⟨ +-identityʳ _ ⟩
        p₃                     ≤⟨ p₃≤ ⟩
        p₄                     ≤⟨ headₘ-monotone (inv-usage-var ▸x) ⟩
        ℓ₀                     ∎ }}}}}}
      where
      open ≤-reasoning

    -- The program t evaluates to zero in the abstract machine (and the
    -- heap is extended in a certain way).

    ⟨t⟩⇒⟨zero⟩ :
      ∀ (H : Heap 0 1) →
      ⟨ H , t , id , ε ⟩ ↠*
      ⟨ H ∙ (𝟘 , var x0 , id)
         ∙ (ℓ₀ · (𝟙 ∧ 𝟘) , var x0 , lift id)
         ∙ (ℓ₀ · 𝟘 , natrec 𝟘 𝟘 𝟘 ℕ (suc zero) zero (var x0) , liftn id 2)
         , zero , liftn id 3 , ε ⟩
    ⟨t⟩⇒⟨zero⟩ H =
      let H₁ = H ∙ (ℓ₀ · 𝟘 , var x0 , id)
          H₁′ = H ∙ (𝟘 , var x0 , id)
          H₁≡H₁′ = cong (λ x → H ∙ (x , var x0 , id)) (·-zeroʳ _)
          H₂ = H₁′ ∙ (ℓ₀ · (𝟙 ∧ 𝟘) , var x0 , lift id)
                   ∙ (ℓ₀ · 𝟘 , natrec 𝟘 𝟘 𝟘 _ _ _ _ , liftn id 2)
          open R
      in
        ⟨ H , t , id , ε ⟩                                                                       ≡⟨⟩↠
        ⟨ H , lam 𝟘 (natcase 𝟘 𝟘 ℕ (suc zero) zero (suc (var x0))) ∘⟨ 𝟘 ⟩ var x0 , id , ε ⟩      ⇒ₑ⟨ appₕ ⟩
        ⟨ H , lam 𝟘 (natcase 𝟘 𝟘 ℕ (suc zero) zero (suc (var x0))) , id , ∘ₑ 𝟘 (var x0) id ∙ ε ⟩ ⇒ᵥ⟨ lamₕ ε ⟩
        ⟨ H₁ , natcase 𝟘 𝟘 ℕ (suc zero) zero (suc (var x0)) , lift id , ε ⟩                      ≡⟨ H₁≡H₁′ ⨾ refl ⨾ refl ⨾ refl ⟩↠
        ⟨ H₁′ , natrec 𝟘 𝟘 𝟘 ℕ (suc zero) (wk1 zero) (suc (var x0)) , lift id , ε ⟩              ⇒ₑ⟨ natrecₕ ⟩
        ⟨ H₁′ , suc (var x0) , lift id , natrecₑ 𝟘 𝟘 𝟘 ℕ (suc zero) zero (lift id) ∙ ε ⟩         ⇒ᵥ⟨ sucₕ ε (no-nrₑ nrᵢ-𝟘-GLB) ⟩
        ⟨ H₂ , zero , liftn id 3 ,  ε ⟩                                                          ∎
