------------------------------------------------------------------------
-- Canonicity theorems for natural numbers and the empty type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality

module Definition.Typed.Consequences.Canonicity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Definition.Untyped M)
  {m} {∇ : DCon (Term 0) m}
  where

open Type-restrictions R

open import Definition.Untyped.Neutral M type-variant

open import Definition.Typed R
import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Fundamental.Reducibility
  R {Γ = glassify ∇ » ε} ⦃ inc = ε ⦄
open import Definition.LogicalRelation.Unary R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Vec using (ε)

private
  variable
    α : Nat
    A t u v : Term _

opaque

  -- Canonicity for natural numbers.

  canonicity : ∇ » ε ⊢ t ∷ ℕ → ∃ λ n → glassify ∇ » ε ⊢ t ≡ sucᵏ n ∷ ℕ
  canonicity {t} ⊢t = $⟨ ⊢t ⟩
    ∇ » ε ⊢ t ∷ ℕ                              →⟨ glassify-⊢∷ ⟩
    glassify ∇ » ε ⊢ t ∷ ℕ                     →⟨ ⊩∷ℕ⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ ⟩
    glassify ∇ » ε ⊩ℕ t ∷ℕ                     →⟨ lemma ⟩
    (∃ λ n → glassify ∇ » ε ⊢ t ≡ sucᵏ n ∷ ℕ)  □
    where
    lemma : glassify ∇ » ε ⊩ℕ u ∷ℕ → ∃ λ n → glassify ∇ » ε ⊢ u ≡ sucᵏ n ∷ ℕ
    lemma (ℕₜ v u⇒*v _ ⊩v) =
      Σ.map idᶠ (trans (subset*Term u⇒*v))
        (case ⊩v of λ where
           (ne (neNfₜ u-ne _)) → ⊥-elim (glass-closed-no-ne u-ne)
           zeroᵣ               → 0 , refl (zeroⱼ (wfTerm (glassify-⊢∷ ⊢t)))
           (sucᵣ ⊩u)           → Σ.map 1+ suc-cong (lemma ⊩u))

opaque

  -- Canonicity for the empty type.

  ¬Empty : ¬ ∇ » ε ⊢ t ∷ Empty
  ¬Empty {t} =
    ∇ » ε ⊢ t ∷ Empty               →⟨ glassify-⊢∷ ⟩
    glassify ∇ » ε ⊢ t ∷ Empty      →⟨ ⊩∷Empty⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ ⟩
    glassify ∇ » ε ⊩Empty t ∷Empty  →⟨ (λ { (Emptyₜ _ _ _ (ne (neNfₜ u-ne _))) →
                                            glass-closed-no-ne u-ne }) ⟩
    ⊥                               □

opaque

  -- There can be no well-typed definition of the empty type.

  ¬defn-Empty : » ∇ → ¬ α ↦ t ∷ Empty ∈ ∇
  ¬defn-Empty »∇ α↦t = ¬Empty (wf-↦∷∈ α↦t »∇)

opaque

  -- Every closed equality proof reduces to rfl.

  ε⊢⇒*rfl∷Id : ∇ » ε ⊢ v ∷ Id A t u → glassify ∇ » ε ⊢ v ⇒* rfl ∷ Id A t u
  ε⊢⇒*rfl∷Id ⊢v =
    case ⊩∷Id⇔ .proj₁ $ reducible-⊩∷ (glassify-⊢∷ ⊢v) .proj₂ of λ
      (_ , v⇒*w , _ , _ , rest) →
    case rest of λ where
      (rflᵣ _)    → v⇒*w
      (ne w-ne _) → ⊥-elim $ glass-closed-no-ne w-ne

opaque

  -- If Id A t u is inhabited in the empty context, then t is
  -- definitionally equal to u at type A.

  ε⊢∷Id→ε⊢≡∷ : ∇ » ε ⊢ v ∷ Id A t u → glassify ∇ » ε ⊢ t ≡ u ∷ A
  ε⊢∷Id→ε⊢≡∷ {v} {A} {t} {u} =
    ∇ » ε ⊢ v ∷ Id A t u                  →⟨ ε⊢⇒*rfl∷Id ⟩
    glassify ∇ » ε ⊢ v ⇒* rfl ∷ Id A t u  →⟨ proj₂ ∘→ proj₂ ∘→ syntacticEqTerm ∘→ subset*Term ⟩
    glassify ∇ » ε ⊢ rfl ∷ Id A t u       →⟨ inversion-rfl-Id ⦃ ok = ε ⦄ ⟩
    glassify ∇ » ε ⊢ t ≡ u ∷ A            □

opaque
  unfolding Trans

  -- In a non-glass empty context, Id A t u being inhabited is not
  -- sufficient to conclude definitional equality.

  ε⊢∷Id↛ε⊢≡∷ :
    Opacity-allowed →
    ∃₅ λ (∇ : DCon (Term 0) 2) A t u v →
    ∇ » ε ⊢ v ∷ Id A t u × ¬ ∇ » ε ⊢ t ≡ u ∷ A
  ε⊢∷Id↛ε⊢≡∷ ok =
    let ∇ = ε ∙⟨ opa ε     ⟩[ zero ∷ ℕ ]
              ∙⟨ opa (ε ¹) ⟩[ rfl  ∷ Id ℕ zero (defn 0) ]
        ⊢ε = ε ∙ᵒ⟨ ok ⟩[ zeroⱼ εε ∷ ℕⱼ εε ]
        ⊢εᵗ = ε ∙ᵗ[ zeroⱼ εε ]
        ⊢Id = Idⱼ (ℕⱼ ⊢ε) (zeroⱼ ⊢ε) (defn ⊢ε here PE.refl)
        ⊢α₀ = defn ⊢εᵗ here PE.refl
        ⊢rfl = conv (rflⱼ ⊢α₀)
                    (Id-cong (refl (ℕⱼ ⊢εᵗ))
                             (δ-red ⊢εᵗ here PE.refl PE.refl)
                             (refl ⊢α₀))
        ⊢α₁ = defn (ε ∙ᵒ⟨ ok ⟩[ ⊢rfl ∷ ⊢Id ]) here PE.refl
        not = I.zero≢ne ⦃ ok = ε ⦄ _ (defn⁺ (there here))
    in  ∇ , ℕ , zero , defn 0 , defn 1 , ⊢α₁ , not
