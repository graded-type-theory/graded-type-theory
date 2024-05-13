------------------------------------------------------------------------
-- If a natural number is in the logical relation, so is its successor.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Successor
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Nat
open import Tools.Product

private
  variable
    m : Nat
    Γ : Con Term m


-- Helper function for successors for specific reducible derivations.
sucTerm′ : ∀ {l n}
           ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
         → Γ ⊩⟨ l ⟩ n ∷ ℕ / ℕ-intr [ℕ]
         → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / ℕ-intr [ℕ]
sucTerm′ (noemb D) (ℕₜ n [ ⊢t , ⊢u , d ] n≡n prop) =
  let natN = natural prop
  in  ℕₜ _ [ sucⱼ ⊢t , sucⱼ ⊢t , id (sucⱼ ⊢t) ]
         (≅-suc-cong (≅ₜ-red (red D) d d ℕₙ
                             (naturalWhnf natN) (naturalWhnf natN) n≡n))
         (sucᵣ (ℕₜ n [ ⊢t , ⊢u , d ] n≡n prop))
sucTerm′ (emb 0<1 x) [n] = sucTerm′ x [n]

-- Reducible natural numbers can be used to construct reducible successors.
sucTerm : ∀ {l n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
        → Γ ⊩⟨ l ⟩ n ∷ ℕ / [ℕ]
        → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / [ℕ]
sucTerm [ℕ] [n] =
  let [n]′ = irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n]
  in  irrelevanceTerm (ℕ-intr (ℕ-elim [ℕ]))
                      [ℕ]
                      (sucTerm′ (ℕ-elim [ℕ]) [n]′)

-- Helper function for successor equality for specific reducible derivations.
sucEqTerm′ : ∀ {l n n′}
             ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ / ℕ-intr [ℕ]
           → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ / ℕ-intr [ℕ]
sucEqTerm′ (noemb D) (ℕₜ₌ k k′ [ ⊢t , ⊢u , d ]
                              [ ⊢t₁ , ⊢u₁ , d₁ ] t≡u prop) =
  let natK , natK′ = split prop
  in  ℕₜ₌ _ _ (idRedTerm:*: (sucⱼ ⊢t)) (idRedTerm:*: (sucⱼ ⊢t₁))
        (≅-suc-cong (≅ₜ-red (red D) d d₁ ℕₙ (naturalWhnf natK) (naturalWhnf natK′) t≡u))
        (sucᵣ (ℕₜ₌ k k′ [ ⊢t , ⊢u , d ] [ ⊢t₁ , ⊢u₁ , d₁ ] t≡u prop))
sucEqTerm′ (emb 0<1 x) [n≡n′] = sucEqTerm′ x [n≡n′]

-- Reducible natural number equality can be used to construct reducible equality
-- of the successors of the numbers.
sucEqTerm : ∀ {l n n′} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
          → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ / [ℕ]
          → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ / [ℕ]
sucEqTerm [ℕ] [n≡n′] =
  let [n≡n′]′ = irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n≡n′]
  in  irrelevanceEqTerm (ℕ-intr (ℕ-elim [ℕ])) [ℕ]
                        (sucEqTerm′ (ℕ-elim [ℕ]) [n≡n′]′)
