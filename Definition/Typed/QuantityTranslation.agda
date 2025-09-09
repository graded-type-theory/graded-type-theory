------------------------------------------------------------------------
-- The quantity translation functions preserve various things related
-- to typing (given certain assumptions)
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Type-restrictions
open import Definition.Typed.Restrictions

module Definition.Typed.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  (R₁ : Type-restrictions 𝕄₁)
  (R₂ : Type-restrictions 𝕄₂)
  (tr tr-Σ : M₁ → M₂)
  (m : Is-morphism 𝕄₁ 𝕄₂ tr)
  (m-Σ : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  (pres : Are-preserving-type-restrictions R₁ R₂ tr tr-Σ)
  where

open Is-morphism m
open Is-Σ-morphism m-Σ
open Are-preserving-type-restrictions pres

open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (inj₁; inj₂)

open import Definition.Typed
open import Definition.Typed.Consequences.Admissible R₂
open import Definition.Typed.Properties R₂
import Definition.Typed.Substitution
open import Definition.Untyped
import Definition.Untyped.Erased
open import Definition.Untyped.QuantityTranslation tr tr-Σ

private
  module E₁ = Definition.Untyped.Erased 𝕄₁
  module E₂ = Definition.Untyped.Erased 𝕄₂
  module R₁ = Type-restrictions R₁
  module R₂ = Type-restrictions R₂
  module T₁ = Definition.Typed R₁
  module T₂ = Definition.Typed R₂
  module S₁ = Definition.Typed.Substitution R₁
  module S₂ = Definition.Typed.Substitution R₂
  module U₁ = Definition.Untyped M₁
  module U₂ = Definition.Untyped M₂

private variable
  x       : Fin _
  ∇ ∇′    : DCon _ _
  Δ       : Con _ _
  Γ       : Cons _ _ _
  A B t u : Term _ _
  σ σ′    : Subst _ _ _
  p q     : M₁
  s       : Strength
  φ       : Unfolding _

opaque

  -- If []-cong is allowed (in the source modality), then tr-Term
  -- commutes with Erased.

  tr-Term-Erased :
    R₁.[]-cong-allowed s →
    E₂.Erased s (tr-Term A) PE.≡ tr-Term (E₁.Erased s A)
  tr-Term-Erased ok =
    PE.sym $ PE.cong₂ (λ p q → Σ p , q ▷ _ ▹ _)
      (tr-Σ-𝟘-≡ (R₁.[]-cong→¬Trivial ok))
      (tr-𝟘-≡ (R₁.[]-cong→¬Trivial ok))

opaque

  -- If []-cong is allowed (in the source modality), then tr-Term
  -- commutes with [_].

  tr-Term-[]′ :
    R₁.[]-cong-allowed s →
    E₂.[_] s (tr-Term t) PE.≡ tr-Term (E₁.[_] s t)
  tr-Term-[]′ ok =
    PE.sym $ PE.cong (λ p → prod _ p _ _) $
    tr-Σ-𝟘-≡ (R₁.[]-cong→¬Trivial ok)

opaque

  -- A combination of the previous two lemmas.

  tr-Term-Id-Erased-[]-[] :
    R₁.[]-cong-allowed s →
    Id (E₂.Erased s (tr-Term A)) (E₂.[_] s (tr-Term t)) (E₂.[_] s (tr-Term u)) PE.≡
    tr-Term (Id (E₁.Erased s A) (E₁.[_] s t) (E₁.[_] s u))
  tr-Term-Id-Erased-[]-[] ok =
    PE.cong₃ Id (tr-Term-Erased ok) (tr-Term-[]′ ok)
      (tr-Term-[]′ ok)

-- Preservation of _∷_∈_.

tr-∷∈ : x T₁.∷ A ∈ Δ → x T₂.∷ tr-Term A ∈ tr-Con Δ
tr-∷∈ here =
  PE.subst (_ T₂.∷_∈ _ ∙ tr-Term _) tr-Term-wk here
tr-∷∈ (there x) =
  PE.subst (_ T₂.∷_∈ _ ∙ tr-Term _) tr-Term-wk (there (tr-∷∈ x))

opaque

  -- The relation _»_↜_ is preserved by tr-DCon.

  tr-↜ : φ T₁.» ∇′ ↜ ∇ → φ T₂.» tr-DCon ∇′ ↜ tr-DCon ∇
  tr-↜ ε                                          = ε
  tr-↜ (∇′↜∇ ⁰)                                   = tr-↜ ∇′↜∇ ⁰
  tr-↜ (∇′↜∇ ¹ᵒ) rewrite unfolding-mode-preserved = tr-↜ ∇′↜∇ ¹ᵒ
  tr-↜ (∇′↜∇ ¹ᵗ)                                  = tr-↜ ∇′↜∇ ¹ᵗ

mutual

  -- Preservation of »_.

  tr-» : T₁.» ∇ → T₂.» tr-DCon ∇
  tr-» ε                        = ε
  tr-» ∙ᵗ[ t ]                  = ∙ᵗ[ tr-⊢∷ t ]
  tr-» ∙ᵒ⟨ ok , ∇′↜∇ ⟩[ t ∷ A ] =
    ∙ᵒ⟨ Opacity-preserved ok , tr-↜ ∇′↜∇ ⟩[ tr-⊢∷ t ∷ tr-⊢′ A ]

  -- Preservation of ⊢_.

  tr-⊢ : T₁.⊢ Γ → T₂.⊢ tr-Cons Γ
  tr-⊢ (ε ∇) = ε (tr-» ∇)
  tr-⊢ (∙ A) = ∙ tr-⊢′ A

  -- Preservation of _⊢_.

  tr-⊢′ : Γ T₁.⊢ A → tr-Cons Γ T₂.⊢ tr-Term A
  tr-⊢′ (Uⱼ Γ) =
    Uⱼ (tr-⊢ Γ)
  tr-⊢′ (ℕⱼ Γ) =
    ℕⱼ (tr-⊢ Γ)
  tr-⊢′ (Emptyⱼ Γ) =
    Emptyⱼ (tr-⊢ Γ)
  tr-⊢′ (Unitⱼ Γ ok) =
    Unitⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢′ (ΠΣⱼ P ok) =
    ΠΣⱼ (tr-⊢′ P) (ΠΣ-preserved ok)
  tr-⊢′ (Idⱼ _ t u) =
    Idⱼ′ (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢′ (univ A) =
    univ (tr-⊢∷ A)

  -- Preservation of _⊢_∷_.

  tr-⊢∷ : Γ T₁.⊢ t ∷ A → tr-Cons Γ T₂.⊢ tr-Term t ∷ tr-Term A
  tr-⊢∷ (defn Γ α PE.refl) =
    defn (tr-⊢ Γ) (tr-↦ α) (PE.sym tr-Term-wk)
  tr-⊢∷ (Uⱼ Γ) =
    Uⱼ (tr-⊢ Γ)
  tr-⊢∷ (ΠΣⱼ {b = b} A P ok) =
    ΠΣⱼ (tr-⊢∷ A) (tr-⊢∷ P) (ΠΣ-preserved ok)
  tr-⊢∷ (ℕⱼ Γ) =
    ℕⱼ (tr-⊢ Γ)
  tr-⊢∷ (Emptyⱼ Γ) =
    Emptyⱼ (tr-⊢ Γ)
  tr-⊢∷ (Unitⱼ Γ ok) =
    Unitⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢∷ (var Γ x) =
    var (tr-⊢ Γ) (tr-∷∈ x)
  tr-⊢∷ (lamⱼ _ t ok) =
    lamⱼ′ (ΠΣ-preserved ok) (tr-⊢∷ t)
  tr-⊢∷ (_∘ⱼ_ {G = P} t u) =
    PE.subst (_ T₂.⊢ _ ∷_) (tr-Term-[] P) (tr-⊢∷ t ∘ⱼ tr-⊢∷ u)
  tr-⊢∷ (prodⱼ {G = P} ⊢P t u ok) =
    prodⱼ (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      (ΠΣ-preserved ok)
  tr-⊢∷ (fstⱼ P t) =
    fstⱼ (tr-⊢′ P) (tr-⊢∷ t)
  tr-⊢∷ (sndⱼ {G = P} ⊢P t) =
    PE.subst (_ T₂.⊢ _ ∷_) (tr-Term-[] P)
      (sndⱼ (tr-⊢′ ⊢P) (tr-⊢∷ t))
  tr-⊢∷ (prodrecⱼ {A = Q} ⊢Q t u ok) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] Q)
      (prodrecⱼ (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ u))
         (ΠΣ-preserved ok))
  tr-⊢∷ (zeroⱼ Γ) =
    zeroⱼ (tr-⊢ Γ)
  tr-⊢∷ (sucⱼ t) =
    sucⱼ (tr-⊢∷ t)
  tr-⊢∷ (natrecⱼ {A = P} z s n) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] P)
      (natrecⱼ
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² P))
            (tr-⊢∷ s))
         (tr-⊢∷ n))
  tr-⊢∷ (emptyrecⱼ A e) =
    emptyrecⱼ (tr-⊢′ A) (tr-⊢∷ e)
  tr-⊢∷ (starⱼ Γ ok) =
    starⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢∷ (unitrecⱼ {A = A} ⊢A t u ok) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] A)
      (unitrecⱼ (tr-⊢′ ⊢A) (tr-⊢∷ t)
        (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
        (Unit-preserved ok))
  tr-⊢∷ (Idⱼ A t u) =
    Idⱼ (tr-⊢∷ A) (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢∷ (rflⱼ t) =
    rflⱼ (tr-⊢∷ t)
  tr-⊢∷ (Jⱼ {B} _ ⊢B u _ w) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[,] B) $
    Jⱼ′
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
      (tr-⊢∷ w)
  tr-⊢∷ (Kⱼ {B} ⊢B u v ok) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] B) $
    Kⱼ (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (tr-⊢∷ v) (K-preserved ok)
  tr-⊢∷ ([]-congⱼ _ _ _ v ok) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-congⱼ′ ([]-cong-preserved ok) (tr-⊢∷ v)
  tr-⊢∷ (conv t A≡B) =
    conv (tr-⊢∷ t) (tr-⊢≡ A≡B)

  -- Preservation of _⊢_≡_.

  tr-⊢≡ : Γ T₁.⊢ A ≡ B → tr-Cons Γ T₂.⊢ tr-Term A ≡ tr-Term B
  tr-⊢≡ (univ A≡B) =
    univ (tr-⊢≡∷ A≡B)
  tr-⊢≡ (refl A) =
    refl (tr-⊢′ A)
  tr-⊢≡ (sym A≡B) =
    sym (tr-⊢≡ A≡B)
  tr-⊢≡ (trans A≡B C≡D) =
    trans (tr-⊢≡ A≡B) (tr-⊢≡ C≡D)
  tr-⊢≡ (ΠΣ-cong {b} A≡B C≡D ok) =
    ΠΣ-cong (tr-⊢≡ A≡B) (tr-⊢≡ C≡D) (ΠΣ-preserved ok)
  tr-⊢≡ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)

  -- Preservation of _⊢_≡_∷_.

  tr-⊢≡∷ :
    Γ T₁.⊢ t ≡ u ∷ A → tr-Cons Γ T₂.⊢ tr-Term t ≡ tr-Term u ∷ tr-Term A
  tr-⊢≡∷ (refl t) =
    refl (tr-⊢∷ t)
  tr-⊢≡∷ (sym _ t≡u) =
    sym′ (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (trans t≡u u≡v) =
    trans (tr-⊢≡∷ t≡u) (tr-⊢≡∷ u≡v)
  tr-⊢≡∷ (conv t≡u A≡B) =
    conv (tr-⊢≡∷ t≡u) (tr-⊢≡ A≡B)
  tr-⊢≡∷ (δ-red Γ α PE.refl PE.refl) =
    δ-red (tr-⊢ Γ) (tr-↦∷ α) (PE.sym tr-Term-wk) (PE.sym tr-Term-wk)
  tr-⊢≡∷ (ΠΣ-cong {b} A≡B C≡D ok) =
    ΠΣ-cong (tr-⊢≡∷ A≡B) (tr-⊢≡∷ C≡D) (ΠΣ-preserved ok)
  tr-⊢≡∷ (app-cong {G = P} t≡u v≡w) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (app-cong (tr-⊢≡∷ t≡u) (tr-⊢≡∷ v≡w))
  tr-⊢≡∷ (β-red {G = P} {t} ⊢P ⊢t u PE.refl ok) =
    PE.subst₂ (T₂._⊢_≡_∷_ _ _)
      (tr-Term-[] t)
      (tr-Term-[] P)
      (β-red (tr-⊢′ ⊢P) (tr-⊢∷ ⊢t) (tr-⊢∷ u) PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ {Γ} (η-eq {F = A} {G = P} _ t u t≡u _) =
    η-eq′ (tr-⊢∷ t) (tr-⊢∷ u)
      (PE.subst₃ (T₂._⊢_≡_∷_ _)
         (PE.sym (PE.cong (_∘⟨ _ ⟩ _ ) tr-Term-wk))
         (PE.sym (PE.cong (_∘⟨ _ ⟩ _ ) tr-Term-wk))
         PE.refl
         (tr-⊢≡∷ t≡u))
  tr-⊢≡∷ (fst-cong P t≡u) =
    fst-cong (tr-⊢′ P) (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (snd-cong {G = P} ⊢P t≡u) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (snd-cong (tr-⊢′ ⊢P) (tr-⊢≡∷ t≡u))
  tr-⊢≡∷ (prod-cong {G = P} {k = s} ⊢P t≡u v≡w ok) =
    prod-cong (tr-⊢′ ⊢P) (tr-⊢≡∷ t≡u)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢≡∷ v≡w))
      (ΠΣ-preserved ok)
  tr-⊢≡∷ (Σ-β₁ {G = P} ⊢P t u PE.refl ok) =
    Σ-β₁ (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      PE.refl (ΠΣ-preserved ok)
  tr-⊢≡∷ (Σ-β₂ {G = P} ⊢P t u PE.refl ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (Σ-β₂ (tr-⊢′ ⊢P) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ (Σ-η {G = P} _ t u t₁≡u₁ t₂≡u₂ _) =
    Σ-η′ (tr-⊢∷ t) (tr-⊢∷ u) (tr-⊢≡∷ t₁≡u₁)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] P))
         (tr-⊢≡∷ t₂≡u₂))
  tr-⊢≡∷ (prodrec-cong {A = Q} Q≡R t≡u v≡w ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] Q)
      (prodrec-cong (tr-⊢≡ Q≡R) (tr-⊢≡∷ t≡u)
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[]↑² Q))
            (tr-⊢≡∷ v≡w))
         (ΠΣ-preserved ok))
  tr-⊢≡∷
    (prodrec-β {G = P} {A = Q} {u = v} ⊢Q t u ⊢v PE.refl ok) =
    PE.subst₂ (T₂._⊢_≡_∷_ _ _) (tr-Term-[,] v) (tr-Term-[] Q)
      (prodrec-β (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² Q))
            (tr-⊢∷ ⊢v))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ (suc-cong t≡u) =
    suc-cong (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (natrec-cong {A = P} P≡P′ z≡z′ s≡s′ n≡n′) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (natrec-cong (tr-⊢≡ P≡P′)
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] P))
            (tr-⊢≡∷ z≡z′))
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[]↑² P))
            (tr-⊢≡∷ s≡s′))
         (tr-⊢≡∷ n≡n′))
  tr-⊢≡∷ (natrec-zero {A = P} z s) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _)
      (tr-Term-[] P)
      (natrec-zero
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² P)) (tr-⊢∷ s)))
  tr-⊢≡∷ (natrec-suc {A = P} {s} z ⊢s n) =
    PE.subst₂ (T₂._⊢_≡_∷_ _ _) (tr-Term-[,] s) (tr-Term-[] P)
      (natrec-suc
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² P)) (tr-⊢∷ ⊢s))
         (tr-⊢∷ n))
  tr-⊢≡∷ (emptyrec-cong A≡B t≡u) =
    emptyrec-cong (tr-⊢≡ A≡B) (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (unitrec-cong {A = A} A≡A′ t≡t′ u≡u′ ok _) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-cong′ (tr-⊢≡ A≡A′) (tr-⊢≡∷ t≡t′)
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] A))
            (tr-⊢≡∷ u≡u′)))
  tr-⊢≡∷ (unitrec-β {A} ⊢A u _ _) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-β-≡ (tr-⊢′ ⊢A)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u)))
  tr-⊢≡∷ (unitrec-β-η {A} ⊢A t u ok₁ ok₂) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-β-η (tr-⊢′ ⊢A) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
         (Unit-preserved ok₁) (Unitʷ-η-preserved ok₂))
  tr-⊢≡∷ (η-unit t u ok) =
    η-unit (tr-⊢∷ t) (tr-⊢∷ u) $
    case ok of λ where
       (inj₁ ok) → inj₁ ok
       (inj₂ ok) → inj₂ (Unitʷ-η-preserved ok)
  tr-⊢≡∷ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (tr-⊢≡∷ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
  tr-⊢≡∷ (J-cong {B₁} {B₂} A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[,] B₁) $
    J-cong′ (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
      (PE.subst₃ T₂._⊢_≡_
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk))
         PE.refl PE.refl $
       tr-⊢≡ B₁≡B₂)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym $ tr-Term-[,] B₁) $
       tr-⊢≡∷ u₁≡u₂)
      (tr-⊢≡∷ v₁≡v₂) (tr-⊢≡∷ w₁≡w₂)
  tr-⊢≡∷ (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] B₁) $
    K-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡ B₁≡B₂)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym $ tr-Term-[] B₁) $
       tr-⊢≡∷ u₁≡u₂)
      (tr-⊢≡∷ v₁≡v₂) (K-preserved ok)
  tr-⊢≡∷ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
      (tr-⊢≡∷ v₁≡v₂) ([]-cong-preserved ok)
  tr-⊢≡∷ (J-β {B} t ⊢B u PE.refl) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[,] B) $
    J-β-≡ (tr-⊢∷ t)
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
  tr-⊢≡∷ (K-β {B} ⊢B u ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] B) $
    K-β (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (K-preserved ok)
  tr-⊢≡∷ ([]-cong-β t PE.refl ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-β (tr-⊢∷ t) PE.refl ([]-cong-preserved ok)
  tr-⊢≡∷ (equality-reflection ok _ v) =
    equality-reflection′ (Equality-reflection-preserved ok) (tr-⊢∷ v)

-- Preservation of _⊢ˢ_∷_.

tr-⊢ˢ∷ : Γ S₁.⊢ˢ σ ∷ Δ → tr-Cons Γ S₂.⊢ˢ tr-Subst σ ∷ tr-Con Δ
tr-⊢ˢ∷ S₁.id                     = S₂.id
tr-⊢ˢ∷ (S₁._,_ {A} ⊢ˢtail ⊢head) =
  tr-⊢ˢ∷ ⊢ˢtail S₂.,
  PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-subst A)) (tr-⊢∷ ⊢head)

-- Preservation of _⊢ˢ_≡_∷_.

tr-⊢ˢ≡∷ :
  Γ S₁.⊢ˢ σ ≡ σ′ ∷ Δ →
  tr-Cons Γ S₂.⊢ˢ tr-Subst σ ≡ tr-Subst σ′ ∷ tr-Con Δ
tr-⊢ˢ≡∷ S₁.id                       = S₂.id
tr-⊢ˢ≡∷ (S₁._,_ {A} ⊢ˢtail≡ ⊢head≡) =
  tr-⊢ˢ≡∷ ⊢ˢtail≡ S₂.,
  PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-subst A)) (tr-⊢≡∷ ⊢head≡)

opaque

  -- Preservation of _⊢ˢʷ_∷_.

  tr-⊢ˢʷ∷ : Γ S₁.⊢ˢʷ σ ∷ Δ → tr-Cons Γ S₂.⊢ˢʷ tr-Subst σ ∷ tr-Con Δ
  tr-⊢ˢʷ∷ = S₂.⊢ˢʷ∷⇔ .proj₂ ∘→ Σ.map tr-⊢ tr-⊢ˢ∷ ∘→ S₁.⊢ˢʷ∷⇔ .proj₁

opaque

  -- Preservation of _⊢ˢʷ_≡_∷_.

  tr-⊢ˢʷ≡∷ :
    Γ S₁.⊢ˢʷ σ ≡ σ′ ∷ Δ →
    tr-Cons Γ S₂.⊢ˢʷ tr-Subst σ ≡ tr-Subst σ′ ∷ tr-Con Δ
  tr-⊢ˢʷ≡∷ =
    S₂.⊢ˢʷ≡∷⇔ .proj₂ ∘→
    Σ.map tr-⊢ (Σ.map tr-⊢ˢ∷ (Σ.map tr-⊢ˢ∷ tr-⊢ˢ≡∷)) ∘→
    S₁.⊢ˢʷ≡∷⇔ .proj₁

-- The following results make use of another assumption.

module _
  (Unitʷ-η-reflected : R₂.Unitʷ-η → R₁.Unitʷ-η)
  where

  -- Preservation of _⊢_⇒_∷_.

  tr-⊢⇒∷ :
    Γ T₁.⊢ t ⇒ u ∷ A →
    tr-Cons Γ T₂.⊢ tr-Term t ⇒ tr-Term u ∷ tr-Term A
  tr-⊢⇒∷ (conv t⇒u A≡B) =
    conv (tr-⊢⇒∷ t⇒u) (tr-⊢≡ A≡B)
  tr-⊢⇒∷ (δ-red ⊢Γ α∈ PE.refl PE.refl) =
    δ-red (tr-⊢ ⊢Γ) (tr-↦∷ α∈) (PE.sym tr-Term-wk) (PE.sym tr-Term-wk)
  tr-⊢⇒∷ (app-subst {G = P} t⇒u v) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (app-subst (tr-⊢⇒∷ t⇒u) (tr-⊢∷ v))
  tr-⊢⇒∷ (β-red {G = P} {t} ⊢P ⊢t u PE.refl ok) =
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[] t) (tr-Term-[] P)
      (β-red (tr-⊢′ ⊢P) (tr-⊢∷ ⊢t) (tr-⊢∷ u) PE.refl (ΠΣ-preserved ok))
  tr-⊢⇒∷ (fst-subst P t⇒u) =
    fst-subst (tr-⊢′ P) (tr-⊢⇒∷ t⇒u)
  tr-⊢⇒∷ (snd-subst {G = P} ⊢P t⇒u) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (snd-subst (tr-⊢′ ⊢P) (tr-⊢⇒∷ t⇒u))
  tr-⊢⇒∷ (Σ-β₁ {G = P} ⊢P t u PE.refl ok) =
    Σ-β₁ (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      PE.refl (ΠΣ-preserved ok)
  tr-⊢⇒∷ (Σ-β₂ {G = P} ⊢P t u PE.refl ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (Σ-β₂ (tr-⊢′ ⊢P) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢⇒∷ (prodrec-subst {A = Q} ⊢Q v t⇒u ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] Q)
      (prodrec-subst (tr-⊢′ ⊢Q)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ v))
         (tr-⊢⇒∷ t⇒u) (ΠΣ-preserved ok))
  tr-⊢⇒∷ (prodrec-β {G = P} {A = Q} {u = v} ⊢Q t u ⊢v PE.refl ok) =
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[,] v) (tr-Term-[] Q)
      (prodrec-β (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² Q)) (tr-⊢∷ ⊢v))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢⇒∷ (natrec-subst {A = P} z s n⇒n′) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (natrec-subst
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² P)) (tr-⊢∷ s))
         (tr-⊢⇒∷ n⇒n′))
  tr-⊢⇒∷ (natrec-zero {A = P} z s) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _)
      (tr-Term-[] P)
      (natrec-zero
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² P)) (tr-⊢∷ s)))
  tr-⊢⇒∷ (natrec-suc {A = P} {s} z ⊢s n) =
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[,] s) (tr-Term-[] P)
      (natrec-suc
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑² P)) (tr-⊢∷ ⊢s))
         (tr-⊢∷ n))
  tr-⊢⇒∷ (emptyrec-subst A t⇒u) =
    emptyrec-subst (tr-⊢′ A) (tr-⊢⇒∷ t⇒u)
  tr-⊢⇒∷ (unitrec-subst {A} ⊢A u t⇒t′ ok₁ ok₂) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-subst (tr-⊢′ ⊢A)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
         (tr-⊢⇒∷ t⇒t′) (Unit-preserved ok₁)
         (ok₂ ∘→ Unitʷ-η-reflected))
  tr-⊢⇒∷ (unitrec-β {A} ⊢A u _ _) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-β-⇒ (tr-⊢′ ⊢A)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u)))
  tr-⊢⇒∷ (unitrec-β-η {A} ⊢A t u ok₁ ok₂) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-β-η (tr-⊢′ ⊢A) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
         (Unit-preserved ok₁) (Unitʷ-η-preserved ok₂))
  tr-⊢⇒∷ (J-subst {B} _ ⊢B u _ w₁⇒w₂) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[,] B) $
    J-subst′
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
      (tr-⊢⇒∷ w₁⇒w₂)
  tr-⊢⇒∷ (K-subst {B} ⊢B u v₁⇒v₂ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] B) $
    K-subst (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (tr-⊢⇒∷ v₁⇒v₂) (K-preserved ok)
  tr-⊢⇒∷ ([]-cong-subst _ _ _ v₁⇒v₂ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-subst′ (tr-⊢⇒∷ v₁⇒v₂) ([]-cong-preserved ok)
  tr-⊢⇒∷ (J-β {B} _ _ t≡t′ ⊢B _ u) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[,] B) $
    J-β-⇒ (tr-⊢≡∷ t≡t′)
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
  tr-⊢⇒∷ (K-β {B} ⊢B u ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] B) $
    K-β (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (K-preserved ok)
  tr-⊢⇒∷ ([]-cong-β _ _ _ t≡t′ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-β-⇒ (tr-⊢≡∷ t≡t′) ([]-cong-preserved ok)

  -- Preservation of _⊢_⇒_.

  tr-⊢⇒ : Γ T₁.⊢ A ⇒ B → tr-Cons Γ T₂.⊢ tr-Term A ⇒ tr-Term B
  tr-⊢⇒ (univ A⇒B) = univ (tr-⊢⇒∷ A⇒B)

  -- Preservation of _⊢_⇒*_∷_.

  tr-⊢⇒*∷ :
    Γ T₁.⊢ t ⇒* u ∷ A →
    tr-Cons Γ T₂.⊢ tr-Term t ⇒* tr-Term u ∷ tr-Term A
  tr-⊢⇒*∷ (id t)       = id (tr-⊢∷ t)
  tr-⊢⇒*∷ (t⇒u ⇨ u⇒*v) = tr-⊢⇒∷ t⇒u ⇨ tr-⊢⇒*∷ u⇒*v

  -- Preservation of _⊢_⇒*_.

  tr-⊢⇒* : Γ T₁.⊢ A ⇒* B → tr-Cons Γ T₂.⊢ tr-Term A ⇒* tr-Term B
  tr-⊢⇒* (id A)       = id (tr-⊢′ A)
  tr-⊢⇒* (A⇒B ⇨ B⇒*C) = tr-⊢⇒ A⇒B ⇨ tr-⊢⇒* B⇒*C

  -- Preservation of _⊢_↘_.

  tr-⊢↘ : Γ T₁.⊢ A ↘ B → tr-Cons Γ T₂.⊢ tr-Term A ↘ tr-Term B
  tr-⊢↘ (A⇒*B , B) = tr-⊢⇒* A⇒*B , tr-Whnf Unitʷ-η-reflected B

  -- Preservation of _⊢_↘_∷_.

  tr-⊢↘∷ :
    Γ T₁.⊢ t ↘ u ∷ A → tr-Cons Γ T₂.⊢ tr-Term t ↘ tr-Term u ∷ tr-Term A
  tr-⊢↘∷ (t⇒*u , u) = tr-⊢⇒*∷ t⇒*u , tr-Whnf Unitʷ-η-reflected u
