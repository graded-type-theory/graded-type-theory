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
  (open Bounded-distributive-lattice L using (⊤; ⊥; ⊥≤))
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
open import Graded.Heap.Reduction.Reasoning type-variant UR factoring-nr ℓ₀
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

open import Definition.Untyped M
open import Definition.Untyped.Nat modality
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed TR

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

------------------------------------------------------------------------
-- The assumption that there are no secret matches is not necessary.
-- That is, there are programs with secret matches that are
-- non-interferent.

opaque

  non-interference-with-secret-matches :
    -- We do not have access to secret information
    -- as otherwise there are no secret matches.
    (𝟘≰ℓ₀ : ¬ 𝟘 ≤ ℓ₀)
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
  non-interference-with-secret-matches 𝟘≰ℓ₀ prodrec-ok Σ-ok =
    _ , t , ε , ε , secret-matches , ▸t , ⊢t
      , λ H₁ H₂ H₁~H₂ ⊢H₁ ▸H₁ →
       _ , _ , _ , _ , _ , _ , ⟨t⟩⇒⟨zero⟩ H₁ , ⟨t⟩⇒⟨zero⟩ H₂ , zeroₙ
         , (H₁~H₂ ∙ (⊥-elim ∘→ 𝟘≰ℓ₀) ∙ (⊥-elim ∘→ 𝟘≰ℓ₀))
    where

    -- The program t corresponds to
    -- let (_ , _) = (zero , zero) in zero
    t : Term 0
    t = prodrec 𝟘 𝟘 𝟘 ℕ (prodʷ 𝟘 zero zero) zero

    secret-matches : ¬ No-secret-matches
    secret-matches nsm =
      𝟘≰ℓ₀ (No-secret-matches.no-secret-prodrec nsm ≤-refl prodrec-ok)

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

    ⊢t : ε » ε ⊢ t ∷ ℕ
    ⊢t =
      let ⊢ℕ = ℕⱼ (∙ ℕⱼ εε)
      in  prodrecⱼ (ℕⱼ (∙ (ΠΣⱼ ⊢ℕ Σ-ok)))
            (prodⱼ ⊢ℕ (zeroⱼ εε) (zeroⱼ εε) Σ-ok)
            (zeroⱼ (∙ ⊢ℕ)) Σ-ok

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
      in
        ⟨ H , t                      , id         , ε ⟩                            ≡⟨⟩↠
        ⟨ H , prodrec 𝟘 𝟘 𝟘 ℕ u zero , id         , ε ⟩                            ⇒ₑ⟨ prodrecₕ ⟩
        ⟨ H , prodʷ 𝟘 zero zero      , id         , prodrecₑ 𝟘 𝟘 𝟘 ℕ zero id ∙ ε ⟩ ⇒ᵥ⟨ prodʷₕ ε ⟩
        ⟨ H′ , zero                  , liftn id 2 , ε ⟩                            ≡⟨ H′≡H″ ⨾ refl ⨾ refl ⨾ refl ⟩↠
        ⟨ H″ , zero                  , liftn id 2 , ε ⟩                            ∎
