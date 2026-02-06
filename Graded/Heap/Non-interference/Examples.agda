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
open import Definition.Typed.Consequences.Reduction TR

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
    ∃₄ λ k (t : Term (1+ k)) γ Δ →
      -- For simplicity, we assume that the heaps contain concrete
      -- values for x0 as opposed to computations (that would evaluate to
      -- values eventually).
      ∀ {H₁ H₂ : Heap 0 k} {ρ : Wk k n} {ρ′ : Wk k m} {p t₁ t₂ q u₁ u₂} →
        let H₁′ : Heap 0 (1+ k)
            H₁′ = H₁ ∙ (p , prodʷ 𝟘 t₁ t₂ , ρ)
            H₂′ : Heap 0 (1+ k)
            H₂′ = H₂ ∙ (q , prodʷ 𝟘 u₁ u₂ , ρ′)
        in  H₁′ ~⟨ ℓ₀ ⟩ H₂′ → γ ▸ʰ H₁′ → ε ⊢ʰ H₁′ ∷ Δ →
      ¬ No-secret-matches ×
      γ ▸[ ℓ₀ ] t ×
      ε » Δ ⊢ t ∷ ℕ ×
      ∃₆ λ m n H₁″ H₂″ (ρ : Wk m n) t′ →
        ⟨ H₁′ , t , id , ε ⟩ ↠* ⟨ H₁″ , t′ , ρ , ε ⟩ ×
        ⟨ H₂′ , t , id , ε ⟩ ↠* ⟨ H₂″ , t′ , ρ , ε ⟩ ×
        Numeral t′ × H₁″ ~⟨ ℓ₀ ⟩ H₂″
  non-interference-with-secret-matches 𝟘≰ℓ₀ prodrec-ok Σ-ok =
    _ , t , 𝟘ᶜ , ε ∙ A , λ { {H₁ = ε} {H₂ = ε} H₁~H₂ ▸H₁ ⊢H₁ →
        case ~⟨⟩-inv-∙ H₁~H₂ of λ {
          (refl , _ , refl , _ , _) →
        secret-matches , ▸t , ⊢t , _ , _ , _ , _
      , _ , zero , ⟨t⟩⇒⟨zero⟩ , ⟨t⟩⇒⟨zero⟩ , zeroₙ
      , (H₁~H₂ ∙ (⊥-elim ∘→ 𝟘≰ℓ₀) ∙ (⊥-elim ∘→ 𝟘≰ℓ₀))}}
    where

    t : Term 1
    t = prodrec 𝟘 𝟘 𝟘 ℕ (var x0) zero

    A : ∀ {n} → Term n
    A = Σʷ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ

    secret-matches : ¬ No-secret-matches
    secret-matches nsm =
      𝟘≰ℓ₀ (No-secret-matches.no-secret-prodrec nsm ≤-refl prodrec-ok)

    ▸t : 𝟘ᶜ ▸[ ℓ₀ ] t
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
      in  sub-≈ᶜ (prodrecₘ var ▸zero ▸ℕ prodrec-ok) $ begin
        𝟘ᶜ                     ≡⟨⟩
        ε ∙ 𝟘                  ≈˘⟨ ε ∙ ·-zeroˡ _ ⟩
        ε ∙ 𝟘 · 𝟘              ≈˘⟨ ε ∙ ·-congˡ (·-zeroʳ _) ⟩
        ε ∙ 𝟘 · ℓ₀ · 𝟘         ≈˘⟨ +ᶜ-identityʳ _ ⟩
        (ε ∙ 𝟘 · ℓ₀ · 𝟘) +ᶜ 𝟘ᶜ ∎
      where
      open ≈ᶜ-reasoning

    ⊢A : ∀ {n} {Δ : Con Term n} → ε »⊢ Δ → ε » Δ ⊢ A
    ⊢A ⊢Δ = ΠΣⱼ (univ (ℕⱼ (∙ univ (ℕⱼ ⊢Δ)))) Σ-ok

    ⊢t : ε » ε ∙ A ⊢ t ∷ ℕ
    ⊢t = prodrecⱼ (univ (ℕⱼ (∙ ⊢A (∙ ⊢A εε))))
           (var (∙ ⊢A εε) here)
           (zeroⱼ (∙ univ (ℕⱼ (∙ univ (ℕⱼ (∙ ⊢A εε))))))
           Σ-ok

    ⟨t⟩⇒⟨zero⟩ :
      ⟨ ε ∙ (p , (prodʷ 𝟘 u v) , ρ) , t , id , ε ⟩ ↠*
      ⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ) ∙ (𝟘 , u , step ρ) ∙ (𝟘 , v , stepn ρ 2) , zero , liftn id 2 , ε ⟩
    ⟨t⟩⇒⟨zero⟩ {p} {u} {v} {ρ} =
      let ∣S∣≡ = subst (∣ prodrecₑ 𝟘 𝟘 𝟘 ℕ zero id ∙ ε ∣≡_)
                   (·-zeroʳ _) (prodrecₑ ∙ ε)
      in
       (⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ)     , t                              , id         , ε ⟩                             ≡⟨⟩↠
        ⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ)     , prodrec 𝟘 𝟘 𝟘 ℕ (var x0) zero  , id         , ε ⟩                             ⇒ₑ⟨ prodrecₕ ⟩
        ⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ)     , var x0                         , id         , prodrecₑ 𝟘 𝟘 𝟘 ℕ zero id ∙ ε ⟩  ⇾ₑ⟨ var ∣S∣≡ (here p-𝟘≡p) ⟩
        ⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ)     , prodʷ 𝟘 u v                    , step ρ     , prodrecₑ 𝟘 𝟘 𝟘 ℕ zero id ∙ ε ⟩  ⇒ᵥ⟨ prodʷₕ ε ⟩
        ⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ)
            ∙ (ℓ₀ · 𝟘 · 𝟘 , u , step ρ)
            ∙ (ℓ₀ · 𝟘 , v , stepn ρ 2)  , zero                           , liftn id 2 , ε ⟩                              ≡⟨ cong₂ (λ x y → (ε ∙ (p , prodʷ 𝟘 u v , ρ) ∙ (x , _)) ∙ (y , _))
                                                                                                                             (PE.trans (·-congˡ (·-zeroʳ _)) (·-zeroʳ _)) (·-zeroʳ _)
                                                                                                                           ⨾ refl ⨾ refl ⨾ refl ⟩↠
        ⟨ ε ∙ (p , prodʷ 𝟘 u v , ρ)
            ∙ (𝟘 , u , step ρ)
            ∙ (𝟘 , v , stepn ρ 2)       , zero                           , liftn id 2 , ε ⟩ ∎)
