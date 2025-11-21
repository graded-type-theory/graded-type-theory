------------------------------------------------------------------------
-- Validity of definitions.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed R
open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Weakening.Definition R

open import Definition.LogicalRelation.Hidden.Restricted R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
import Tools.Level as L
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum
open import Tools.Unit

private
  variable
    n α : Nat
    ∇ ∇′ : DCon (Term 0) _
    φ : Unfolding _
    Γ : Con Term _
    t t′ u A B : Term _
    l l′ : Universe-level
    p : M

------------------------------------------------------------------------
-- Validity of definition contexts

opaque

  -- Valid definition contexts.

  »ᵛ_ : DCon (Term 0) n → Set a
  »ᵛ ε = L.Lift _ ⊤
  »ᵛ (∇ ∙⟨ opa φ ⟩[ t ∷ A ]) =
    »ᵛ ∇ ×
    Opacity-allowed ×
    (∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ A ×
     (Trans φ ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A))
  »ᵛ (∇ ∙⟨ tra ⟩[ t ∷ A ]) = »ᵛ ∇ × ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A

opaque
  unfolding »ᵛ_

  -- A characterisation lemma for »ᵛ_.

  »ᵛε⇔ : »ᵛ ε ⇔ ⊤
  »ᵛε⇔ = _

opaque
  unfolding »ᵛ_

  -- A characterisation lemma for »ᵛ_.

  »ᵛ∙ᵒ⇔ :
    »ᵛ ∇ ∙⟨ opa φ ⟩[ t ∷ A ] ⇔
    (»ᵛ ∇ ×
     Opacity-allowed ×
     (∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ A ×
      (Trans φ ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A)))
  »ᵛ∙ᵒ⇔ = id⇔

opaque
  unfolding »ᵛ_

  -- A characterisation lemma for »ᵛ_.

  »ᵛ∙ᵗ⇔ : »ᵛ ∇ ∙⟨ tra ⟩[ t ∷ A ] ⇔ (»ᵛ ∇ × ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A)
  »ᵛ∙ᵗ⇔ = id⇔

opaque

  -- An introduction lemma for »ᵛ_.

  »ᵛ-∙ᵒ-intro :
    »ᵛ ∇ →
    Opacity-allowed →
    ∇ » ε ⊩ᵛ⟨ l ⟩ A →
    Trans φ ∇ » ε ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    »ᵛ ∇ ∙⟨ opa φ ⟩[ t ∷ A ]
  »ᵛ-∙ᵒ-intro {l} {l′} »∇ ok ⊩A ⊩t =
    »ᵛ∙ᵒ⇔ .proj₂
      (»∇ , ok , l′ ⊔ᵘ l , emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩A , emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t)

opaque

  -- An introduction lemma for »ᵛ_.

  »ᵛ-∙ᵗ-intro : »ᵛ ∇ → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A → »ᵛ ∇ ∙⟨ tra ⟩[ t ∷ A ]
  »ᵛ-∙ᵗ-intro {l} »∇ ⊩t = »ᵛ∙ᵗ⇔ .proj₂ (»∇ , l , ⊩t)

private instance

  ε-inc : Var-included or-empty (ε {A = Term})
  ε-inc = ε

opaque

  -- A well-formedness lemma for _↦∷_∈_.

  wf-↦∈ᵛ : α ↦∷ A ∈ ∇ → »ᵛ ∇ → ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ A
  wf-↦∈ᵛ {∇ = ε} ()
  wf-↦∈ᵛ {∇ = ∇ ∙⟨ opa φ ⟩[ t ∷ A ]} here »∇ =
    let _ , ok , l , ⊩A , ⊩t = »ᵛ∙ᵒ⇔ .proj₁ »∇
    in  l , defn-wk-⊩ᵛ (stepᵒ₁ ok (escape-⊩ᵛ ⊩A) (escape-⊩ᵛ∷ ⊩t)) ⊩A
  wf-↦∈ᵛ {∇ = ∇ ∙⟨ tra ⟩[ t ∷ A ]} here »∇ =
    let _ , l , ⊩t = »ᵛ∙ᵗ⇔ .proj₁ »∇
    in  l , defn-wk-⊩ᵛ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩t)) (wf-⊩ᵛ∷ ⊩t)
  wf-↦∈ᵛ {∇ = ∇ ∙⟨ opa φ ⟩[ t ∷ A ]} (there α↦t) »∇ =
    let »∇′ , ok , _ , ⊩B , ⊩u = »ᵛ∙ᵒ⇔ .proj₁ »∇
        l , ⊩A = wf-↦∈ᵛ α↦t »∇′
    in  l , defn-wk-⊩ᵛ (stepᵒ₁ ok (escape-⊩ᵛ ⊩B) (escape-⊩ᵛ∷ ⊩u)) ⊩A
  wf-↦∈ᵛ {∇ = ∇ ∙⟨ tra ⟩[ t ∷ A ]} (there α↦t) »∇ =
    let »∇′ , _ , ⊩u = »ᵛ∙ᵗ⇔ .proj₁ »∇
        l , ⊩A = wf-↦∈ᵛ α↦t »∇′
    in  l , defn-wk-⊩ᵛ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩u)) ⊩A

opaque

  -- A well-formedness lemma for _↦_∷_∈_.

  wf-↦∷∈ᵛ : α ↦ t ∷ A ∈ ∇ → »ᵛ ∇ → ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A
  wf-↦∷∈ᵛ {∇ = ε} ()
  wf-↦∷∈ᵛ {∇ = ∇ ∙⟨ tra ⟩[ t ∷ A ]} here »∇ =
    let _ , l , ⊩t = »ᵛ∙ᵗ⇔ .proj₁ »∇
    in  l , defn-wk-⊩ᵛ∷ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩t)) ⊩t
  wf-↦∷∈ᵛ {∇ = ∇ ∙⟨ opa φ ⟩[ t ∷ A ]} (there α↦t) »∇ =
    let »∇′ , ok , _ , ⊩B , ⊩u = »ᵛ∙ᵒ⇔ .proj₁ »∇
        l , ⊩t = wf-↦∷∈ᵛ α↦t »∇′
    in  l , defn-wk-⊩ᵛ∷ (stepᵒ₁ ok (escape-⊩ᵛ ⊩B) (escape-⊩ᵛ∷ ⊩u)) ⊩t
  wf-↦∷∈ᵛ {∇ = ∇ ∙⟨ tra ⟩[ t ∷ A ]} (there α↦t) »∇ =
    let »∇′ , _ , ⊩u = »ᵛ∙ᵗ⇔ .proj₁ »∇
        l , ⊩t = wf-↦∷∈ᵛ α↦t »∇′
    in  l , defn-wk-⊩ᵛ∷ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩u)) ⊩t

opaque

  -- An escape lemma for »ᵛ_.

  escape-»ᵛ : »ᵛ ∇ → » ∇
  escape-»ᵛ {∇ = ε} »∇ = ε
  escape-»ᵛ {∇ = ∇ ∙⟨ opa φ ⟩[ t ∷ A ]} »∇ =
    let _ , ok , _ , ⊩A , ⊩t = »ᵛ∙ᵒ⇔ .proj₁ »∇
    in  ∙ᵒ⟨ ok ⟩[ escape-⊩ᵛ∷ ⊩t ∷ escape-⊩ᵛ ⊩A ]
  escape-»ᵛ {∇ = ∇ ∙⟨ tra ⟩[ t ∷ A ]} »∇ =
    ∙ᵗ[ escape-⊩ᵛ∷ (»ᵛ∙ᵗ⇔ .proj₁ »∇ .proj₂ .proj₂) ]

------------------------------------------------------------------------
-- Validity theorems for definitions

opaque

  -- Validity of δ-reduction.

  δ-redᵛ :
    α ↦ t ∷ A ∈ ∇ →
    »ᵛ ∇ →
    ∇ »⊩ᵛ Γ →
    ∃ λ l → ∇ » Γ ⊩ᵛ⟨ l ⟩ defn α ≡ wk wk₀ t ∷ wk wk₀ A
  δ-redᵛ {α} {t} {A} {∇} {Γ} α↦t »∇ ⊩Γ =
    let l , ⊩t = wf-↦∷∈ᵛ α↦t »∇

        α⇒t : ∀ {κ′} {∇′ : DCon (Term 0) κ′} (ξ⊇ : » ∇′ ⊇ ∇)
                {m Δ} {σ : Subst m _} ⦃ inc : Var-included or-empty Δ ⦄
              → ∇′ » Δ ⊩ˢ σ ∷ Γ
              → ∇′ » Δ ⊢ defn α [ σ ] ⇒ wk wk₀ t [ σ ] ∷ wk wk₀ A [ σ ]
        α⇒t ξ⊇ ⊩σ = PE.subst₂ (_ ⊢ defn α ⇒_∷_)
                              (PE.sym wk-wk₀-[]≡)
                              (PE.sym wk-wk₀-[]≡)
                              (δ-red (escape-⊩ˢ∷ ⊩σ .proj₁)
                                     (there*-↦∷∈ ξ⊇ α↦t)
                                     PE.refl PE.refl)

    in  l , ⊩ᵛ∷-⇐ α⇒t (wk-⊩ᵛ∷ wk₀∷⊇ ⊩Γ ⊩t)

opaque

  -- Validity of definitions.

  defnᵛ :
    α ↦∷ A ∈ ∇ →
    »ᵛ ∇ →
    ∇ »⊩ᵛ Γ →
    ∃ λ l → ∇ » Γ ⊩ᵛ⟨ l ⟩ defn α ∷ wk wk₀ A
  defnᵛ {α} {A} {∇} {Γ} α↦ »∇ ⊩Γ = case dichotomy-↦∈ α↦ of λ where
    (inj₁ (t , α↦t)) → let l , α≡t = δ-redᵛ α↦t »∇ ⊩Γ
                       in  l , wf-⊩ᵛ≡∷ α≡t .proj₁
    (inj₂ α↦⊘)       →
      let α↦∷ = ↦⊘∈⇒↦∈ α↦⊘
          l , ⊩A = wf-↦∈ᵛ α↦∷ »∇

          α[]≡α[] : ∀ {κ′} {∇′ : DCon (Term 0) κ′} (ξ⊇ : » ∇′ ⊇ ∇)
                      {m Δ} {σ₁ σ₂ : Subst m _} (σ₁≡σ₂ : ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ)
                    → ∇′ » Δ ⊩⟨ l ⟩ defn α [ σ₁ ] ≡ defn α [ σ₂ ] ∷ wk wk₀ A [ σ₁ ]
          α[]≡α[] ξ⊇ σ₁≡σ₂ = with-inc-⊩≡∷ $
            let ⊢Δ = escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁
                ⊩ᴿA = wk-⊩ (wk₀∷ʷ⊇ ⊢Δ) (defn-wk-⊩ ξ⊇ (⊩ᵛ→⊩ ⊩A))
                α-ne = defnᵃ (there*-↦⊘∈ ξ⊇ α↦⊘)
                A~A = ~-defn (defn ⊢Δ (there*-↦∈ ξ⊇ α↦∷) PE.refl)
                             (there*-↦⊘∈ ξ⊇ α↦⊘)
            in  refl-⊩≡∷ (PE.subst (_ ⊩⟨ l ⟩ defn α ∷_)
                                   (PE.sym wk-wk₀-[]≡)
                                   (neutral-⊩∷ ⊩ᴿA α-ne A~A))

      in  l , ⊩ᵛ∷⇔ .proj₂ (wk-⊩ᵛ wk₀∷⊇ ⊩Γ ⊩A , α[]≡α[])
