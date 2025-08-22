------------------------------------------------------------------------
-- An investigation into necessary assumptions for subject reduction
-- to hold.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
import Graded.Mode

module Graded.Reduction.Necessary
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  (open Type-restrictions TR)
  (open Usage-restrictions UR)
  (open Modality 𝕄)
  (open Graded.Mode 𝕄)
  (Unitʷ-η→ :
     ∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘)
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Restrictions.Natrec 𝕄
import Graded.Reduction TR UR as R
import Graded.Usage 𝕄 UR as U
import Graded.Usage.Inversion 𝕄 UR as UI
import Graded.Usage.Properties 𝕄 UR as UP
import Graded.Usage.Weakening 𝕄 UR as UW

open import Definition.Typed TR
open import Definition.Typed.Properties TR
import Definition.Typed.Reasoning.Type TR as TEq
open import Definition.Typed.Substitution TR
open import Definition.Typed.Weakening TR as W hiding (wk)
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Normal-form M type-variant

open import Tools.Bool using (T; true; false)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+; 2+; 3+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n i : Nat
  l : Universe-level
  Γ : Cons _ _
  Δ : Con Term _
  γ δ η θ : Conₘ _
  t u v z s k A B : Term _
  m : Mode
  p q r : M
  ρ : Wk _ _
  x : Fin _

------------------------------------------------------------------------
-- "Arbitrary" usage relations satisfying some properties.

-- A usage relation with some requirements

record Usage-relation : Set (lsuc a) where
  no-eta-equality
  infix 10 _▸[_]_ ▸[_]_
  field
    _▸[_]_ : Conₘ n → Mode → Term n → Set a

  -- Well-resourced definitions

  ▸[_]_ : Mode → DCon (Term 0) n → Set a
  ▸[ m ] ∇ = ∀ {α t A} → α ↦ t ∷ A ∈ ∇ → ε ▸[ m ] t

  field
    -- "Usage rules"

    varₘ : (𝟘ᶜ , x ≔ ⌜ m ⌝) ▸[ m ] var x
    zeroₘ : 𝟘ᶜ {n = n} ▸[ m ] zero
    sucₘ : γ ▸[ m ] t → γ ▸[ m ] suc t
    starʷₘ : 𝟘ᶜ {n = n} ▸[ m ] starʷ l
    prodʷₘ : γ ▸[ m ᵐ· p ] t → δ ▸[ m ] u → p ·ᶜ γ +ᶜ δ ▸[ m ] prodʷ p t u
    Uₘ : 𝟘ᶜ {n = n} ▸[ m ] U l
    ℕₘ : 𝟘ᶜ {n = n} ▸[ m ] ℕ
    Unitʷₘ : 𝟘ᶜ {n = n} ▸[ m ] Unitʷ l
    Σʷₘ : γ ▸[ m ᵐ· p ] A → δ ∙ ⌜ m ⌝ · q ▸[ m ] B → γ +ᶜ δ ▸[ m ] Σʷ p , q ▷ A ▹ B
    sub : γ ▸[ m ] t → δ ≤ᶜ γ → δ ▸[ m ] t

    -- "Inversion lemmas"
    inv-usage-var :
      γ ▸[ m ] var x → γ ≤ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)
    inv-usage-zero :
      γ ▸[ m ] zero → γ ≤ᶜ 𝟘ᶜ
    inv-usage-suc :
      γ ▸[ m ] suc t → ∃ λ δ → δ ▸[ m ] t × γ ≤ᶜ δ
    inv-usage-starʷ :
      γ ▸[ m ] starʷ l → γ ≤ᶜ 𝟘ᶜ
    inv-usage-prodʷ :
      γ ▸[ m ] prodʷ p t u →
      ∃₂ λ δ η → δ ▸[ m ᵐ· p ] t × η ▸[ m ] u × γ ≤ᶜ p ·ᶜ δ +ᶜ η

    -- Properties of the usage relation
    wkUsage : γ ▸[ m ] t → wkConₘ ρ γ ▸[ m ] wk ρ t
    wkUsage⁻¹ : γ ▸[ m ] wk ρ t → wkConₘ⁻¹ ρ γ ▸[ m ] t
    ▸-𝟘 : ∀ {ok} → γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t

    -- Subject reduction
    usagePresTerm :
      ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u

opaque

  -- The type Usage-relation is inhabited by the usual usage relation

  ▸[]-Usage-relation : Usage-relation
  ▸[]-Usage-relation = record
    { _▸[_]_ = U._▸[_]_
    ; varₘ = U.var
    ; zeroₘ = U.zeroₘ
    ; sucₘ = U.sucₘ
    ; starʷₘ = U.starʷₘ
    ; prodʷₘ = U.prodʷₘ
    ; Uₘ = U.Uₘ
    ; ℕₘ = U.ℕₘ
    ; Unitʷₘ = U.Unitₘ
    ; Σʷₘ = U.ΠΣₘ
    ; sub = U.sub
    ; inv-usage-var = UI.inv-usage-var
    ; inv-usage-zero = UI.inv-usage-zero
    ; inv-usage-suc = λ ▸t →
      let UI.invUsageSuc ▸t′ γ≤ = UI.inv-usage-suc ▸t
      in  _ , ▸t′ , γ≤
    ; inv-usage-starʷ = UI.inv-usage-starʷ
    ; inv-usage-prodʷ = λ ▸t →
        let UI.invUsageProdʷ ▸t₁ ▸t₂ γ≤ = UI.inv-usage-prodʷ ▸t
        in  _ , _ , ▸t₁ , ▸t₂ , γ≤
    ; wkUsage = UW.wkUsage _
    ; wkUsage⁻¹ = UW.wkUsage⁻¹
    ; ▸-𝟘 = UP.▸-𝟘
    ; usagePresTerm = R.usagePresTerm Unitʷ-η→
    }

-- A usage relation with a usage rule for natrec on a certain form.

record Usage-relation-natrec₁ : Set (lsuc a) where
  no-eta-equality
  field
    usage-relation : Usage-relation

  open Usage-relation usage-relation public
  field

    -- Ansatz for usage rule for natrec
    f : (p r : M) → M
    g : (p r : M) (γ δ : Conₘ n) → Conₘ n
    natrecₘ :
      γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
      η ▸[ m ] k → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
      f p r ·ᶜ η +ᶜ g p r γ δ ▸[ m ] natrec p q r A z s k
    inv-usage-natrec :
      γ ▸[ m ] natrec p q r A z s k →
      ∃₄ λ δ₁ δ₂ δ₃ δ₄ →
      δ₁ ▸[ m ] z × δ₂ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
      δ₃ ▸[ m ] k × δ₄ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A ×
      γ ≤ᶜ f p r ·ᶜ δ₃ +ᶜ g p r δ₁ δ₂

opaque
  unfolding ▸[]-Usage-relation

  factoring-nr-Usage-relation :
    ⦃ has-nr : Nr-available ⦄
    ⦃ nr-factoring : Is-factoring-nr _ (Natrec-mode-Has-nr has-nr) ⦄ →
    Usage-relation-natrec₁
  factoring-nr-Usage-relation ⦃ has-nr ⦄ ⦃ nr-factoring ⦄ = record
    { usage-relation = ▸[]-Usage-relation
    ; f = nr₂
    ; g = λ p r γ δ → nrᶜ p r γ δ 𝟘ᶜ
    ; natrecₘ = λ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} ▸z ▸s ▸n ▸A →
        U.sub (U.natrecₘ ▸z ▸s ▸n ▸A)
          (≤ᶜ-reflexive (≈ᶜ-sym nrᶜ-factoring))
    ; inv-usage-natrec = λ ▸nr →
        let δ₁ , δ₂ , δ₃ , δ₄ , ▸z , ▸s , ▸n , ▸A , γ≤ = UI.inv-usage-natrec-has-nr ▸nr
        in  δ₁ , δ₂ , δ₃ , δ₄ , ▸z , ▸s , ▸n , ▸A
               , ≤ᶜ-trans γ≤ (≤ᶜ-reflexive nrᶜ-factoring)
    }
    where
    open Is-factoring-nr nr-factoring

-- A usage relation with a usage rule for natrec on a certain form.
-- This ansatz is similar to the one above but the function g does
-- not depend on the grade p.

record Usage-relation-natrec₂ : Set (lsuc a) where
  no-eta-equality
  field
    usage-relation : Usage-relation

  open Usage-relation usage-relation public
  field

    -- Ansatz for usage rule for natrec
    f : (p r : M) → M
    g : (r : M) (γ δ : Conₘ n) → Conₘ n
    natrecₘ :
      γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
      η ▸[ m ] k → θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
      f p r ·ᶜ η +ᶜ g r γ δ ▸[ m ] natrec p q r A z s k
    inv-usage-natrec :
      γ ▸[ m ] natrec p q r A z s k →
      ∃₄ λ δ₁ δ₂ δ₃ δ₄ →
      δ₁ ▸[ m ] z × δ₂ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
      δ₃ ▸[ m ] k × δ₄ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A ×
      γ ≤ᶜ f p r ·ᶜ δ₃ +ᶜ g r δ₁ δ₂

opaque

  -- The second ansatz for natrec is a special case of the first.

  Natrec₂→Natrec₁ :
    Usage-relation-natrec₂ → Usage-relation-natrec₁
  Natrec₂→Natrec₁ r = record
    { usage-relation = usage-relation
    ; f = f
    ; g = λ p r γ δ → g r γ δ
    ; natrecₘ = natrecₘ
    ; inv-usage-natrec = inv-usage-natrec
    }
    where
    open Usage-relation-natrec₂ r

------------------------------------------------------------------------
-- Some terms and lemmas used in proofs below.

private

  opaque

    -- A term with a given best usage context.

    sink : Conₘ n → Term n
    sink ε = starʷ 0
    sink (γ ∙ p) = prodʷ p (var x0) (wk1 (sink γ))

  opaque
    unfolding sink

    -- sink for the empty context is the unit element.

    sink-ε-≡ : sink ε PE.≡ starʷ 0
    sink-ε-≡ = PE.refl

  opaque
    unfolding sink

    -- sink for a non-empty context is a pair.

    sink-∙-≡ : sink (γ ∙ p) PE.≡ prodʷ p (var x0) (wk1 (sink γ))
    sink-∙-≡ = PE.refl

  opaque

    -- The type of sink under a given typing context.

    Sink : Con Term n → Conₘ n → Term n
    Sink ε ε = Unitʷ 0
    Sink (Γ ∙ A) (γ ∙ p) = Σʷ p , 𝟘 ▷ wk1 A ▹ wk₂ (Sink Γ γ)

  opaque
    unfolding Sink

    -- Sink for the empty context is the unit type.

    Sink-ε-≡ : Sink ε ε PE.≡ Unitʷ 0
    Sink-ε-≡ = PE.refl

  opaque
    unfolding Sink

    -- Sink for a non-empty context is a Σ-type.

    Sink-∙-≡ : Sink (Δ ∙ A) (γ ∙ p) PE.≡ Σʷ p , 𝟘 ▷ wk1 A ▹ wk₂ (Sink Δ γ)
    Sink-∙-≡ = PE.refl

  opaque

    -- A Type-restriction for Sink

    Sink-allowed : Conₘ n → Set a
    Sink-allowed ε       = Unitʷ-allowed
    Sink-allowed (γ ∙ p) = Sink-allowed γ × Σʷ-allowed p 𝟘

  opaque
    unfolding Sink-allowed

    -- Sink is a well-formed type

    ⊢-Sink :
      ⊢ Γ → Sink-allowed γ → Γ ⊢ Sink (Γ .vars) γ
    ⊢-Sink {γ = ε} (ε »d) ok =
      ⊢-cong (Unitⱼ (ε »d) ok) (PE.sym Sink-ε-≡)
    ⊢-Sink {γ = γ ∙ p} (∙ ⊢A) (ok₁ , ok₂) =
      ⊢-cong
        (ΠΣⱼ (W.wk (stepʷ (step id) (W.wk (stepʷ id ⊢A) ⊢A)) (⊢-Sink (wf ⊢A) ok₁)) ok₂)
        (PE.sym Sink-∙-≡)

  opaque
    unfolding Sink-allowed

    -- sink is a well-formed term of type Sink.

    ⊢∷-sink : ⊢ Γ → Sink-allowed γ → Γ ⊢ sink γ ∷ Sink (Γ .vars) γ
    ⊢∷-sink {γ = ε} (ε »d) ok =
      ⊢∷-conv-PE (⊢∷-cong (starⱼ (ε »d) ok) (PE.sym sink-ε-≡))
        (PE.sym Sink-ε-≡)
    ⊢∷-sink {γ = γ ∙ p} (∙ ⊢A) (ok₁ , ok₂) =
     let ⊢t = ⊢∷-conv-PE (wkTerm (stepʷ id ⊢A) (⊢∷-sink (wf ⊢A) ok₁))
                (PE.sym (step-sgSubst _ _))
         ⊢B = W.wk (stepʷ (step id) (W.wk (stepʷ id ⊢A) ⊢A))
                (⊢-Sink (wf ⊢A) ok₁)
     in  ⊢∷-conv-PE
           (⊢∷-cong (prodⱼ ⊢B (var (∙ ⊢A) here) ⊢t ok₂)
             (PE.sym sink-∙-≡))
           (PE.sym Sink-∙-≡)

  -- A context used in some proofs below consisting only of ℕ.

  Γᴺ : Cons 0 n
  Γᴺ {n = 0} = ε » ε
  Γᴺ {n = 1+ n} = Γᴺ »∙ ℕ

  Δᴺ : Con Term n
  Δᴺ = Γᴺ .vars

  opaque

    -- The context Γᴺ is well-formed.

    ⊢Γᴺ : ⊢ (Γᴺ {n = n})
    ⊢Γᴺ {n = 0} = εε
    ⊢Γᴺ {n = 1+ n} = ∙ ℕⱼ ⊢Γᴺ

  opaque
    unfolding Sink-allowed

    -- Sink is a well-formed term of type U 0 under Γᴺ.

    ⊢∷-Sink-Γᴺ : Sink-allowed γ → Γᴺ ⊢ Sink Δᴺ γ ∷ U 0
    ⊢∷-Sink-Γᴺ {γ = ε} ok =
      ⊢∷-cong (Unitⱼ εε ok) (PE.sym Sink-ε-≡)
    ⊢∷-Sink-Γᴺ {γ = γ ∙ p} (ok₁ , ok₂) =
      ⊢∷-cong
        (ΠΣⱼ (ℕⱼ ⊢Γᴺ) (wkTerm (stepʷ (step id) (ℕⱼ ⊢Γᴺ)) (⊢∷-Sink-Γᴺ ok₁)) ok₂)
        (PE.sym Sink-∙-≡)

------------------------------------------------------------------------
-- Usage properties that hold for "arbitrary" usage relations.

module Usage (usage : Usage-relation) where

  open Usage-relation usage

  opaque

    -- A usage rule for sucᵏ.

    ▸sucᵏ : ∀ i → 𝟘ᶜ {n = n} ▸[ m ] sucᵏ i
    ▸sucᵏ 0 = zeroₘ
    ▸sucᵏ (1+ i) = sucₘ (▸sucᵏ i)

  opaque

    -- A usage inversion lemma for sucᵏ.

    inv-usage-sucᵏ : γ ▸[ m ] sucᵏ i → γ ≤ᶜ 𝟘ᶜ
    inv-usage-sucᵏ {i = 0} ▸i =
      inv-usage-zero ▸i
    inv-usage-sucᵏ {i = 1+ i} ▸i =
      let _ , ▸j , γ≤ = inv-usage-suc ▸i
      in  ≤ᶜ-trans γ≤ (inv-usage-sucᵏ ▸j)

  opaque

    -- A usage rule for Sink Δᴺ.

    ▸Sink-Δᴺ : 𝟘ᶜ ▸[ m ] Sink Δᴺ γ
    ▸Sink-Δᴺ {γ = ε} =
      PE.subst (_▸[_]_ _ _) (PE.sym Sink-ε-≡) Unitʷₘ
    ▸Sink-Δᴺ {γ = γ ∙ p} =
      PE.subst (_▸[_]_ _ _) (PE.sym Sink-∙-≡)
        (sub (Σʷₘ ℕₘ
               (sub (wkUsage ▸Sink-Δᴺ)
                 (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroʳ _))))
          (≤ᶜ-reflexive (≈ᶜ-sym (+ᶜ-identityʳ _))))

  opaque

    -- A usage rule for sink: sink γ is well-resourced under context γ
    -- (at mode 𝟙ᵐ).

    ▸sink : (γ : Conₘ n) → γ ▸[ 𝟙ᵐ ] sink γ
    ▸sink ε =
      PE.subst (_▸[_]_ _ _) (PE.sym sink-ε-≡) starʷₘ
    ▸sink (γ ∙ p) =
      let open ≤ᶜ-reasoning
          ▸t = sub (prodʷₘ varₘ (wkUsage (▸sink γ))) $ begin
            γ            ∙ p                      ≈˘⟨ +ᶜ-identityˡ _ ∙ ·⌜⌞⌟⌝ ⟩
            𝟘ᶜ +ᶜ γ      ∙ p · ⌜ ⌞ p ⌟ ⌝          ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ∙ +-identityʳ _ ⟩
            p ·ᶜ 𝟘ᶜ +ᶜ γ ∙ p · ⌜ ⌞ p ⌟ ⌝ + 𝟘      ≡⟨⟩
            p ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ (γ ∙ 𝟘) ∎
      in  PE.subst (_▸[_]_ _ _) (PE.sym sink-∙-≡) ▸t

  opaque

    -- A usage inversion lemma for sink γ applied to a weakening.

    inv-usage-sink-wk : δ ▸[ m ] wk ρ (sink γ) → δ ≤ᶜ ⌜ m ⌝ ·ᶜ (wkConₘ ρ γ)
    inv-usage-sink-wk {δ} {m} {ρ} {γ = ε} ▸t = begin
      δ                    ≤⟨ inv-usage-starʷ (PE.subst (λ x → δ ▸[ m ] x) (PE.cong (wk ρ) sink-ε-≡) ▸t) ⟩
      𝟘ᶜ                   ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
      ⌜ m ⌝ ·ᶜ 𝟘ᶜ          ≡˘⟨ PE.cong (⌜ m ⌝ ·ᶜ_) (wk-𝟘ᶜ ρ) ⟩
      ⌜ m ⌝ ·ᶜ wkConₘ ρ 𝟘ᶜ ≡⟨⟩
      ⌜ m ⌝ ·ᶜ wkConₘ ρ ε  ∎
      where
      open ≤ᶜ-reasoning
    inv-usage-sink-wk {δ} {m} {ρ} {γ = γ ∙ p} ▸t =
      let ▸t′ = PE.subst (λ x → δ ▸[ m ] x) (PE.cong (wk ρ) sink-∙-≡) ▸t
          δ₁ , δ₂ , ▸x , ▸γ , δ≤ = inv-usage-prodʷ ▸t′
          ▸γ′ = PE.subst (λ x → δ₂ ▸[ m ] x) (wk-comp ρ (step id) (sink γ)) ▸γ
          δ₂≤ = inv-usage-sink-wk ▸γ′
      in  begin
        δ                                                                               ≤⟨ δ≤ ⟩
        p ·ᶜ δ₁ +ᶜ δ₂                                                                   ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var ▸x)) δ₂≤ ⟩
        p ·ᶜ (𝟘ᶜ , wkVar ρ x0 ≔ ⌜ m ᵐ· p ⌝) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ (ρ • step id) γ          ≡˘⟨ PE.cong (λ x → p ·ᶜ (x , _ ≔ _) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ (ρ • step id) γ)
                                                                                            (wk-𝟘ᶜ ρ) ⟩
        p ·ᶜ (wkConₘ ρ 𝟘ᶜ , wkVar ρ x0 ≔ ⌜ m ᵐ· p ⌝) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ (ρ • step id) γ ≡˘⟨ PE.cong₂ (λ x y → p ·ᶜ x +ᶜ ⌜ m ⌝ ·ᶜ y)
                                                                                             (wk-,≔ ρ) (PE.sym (wk-•ᶜ ρ _)) ⟩
        p ·ᶜ wkConₘ ρ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· p ⌝) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (wkConₘ (step id) γ)  ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _))) ⟩
        p ·ᶜ wkConₘ ρ (⌜ m ᵐ· p ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙)) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
        p ·ᶜ ⌜ m ᵐ· p ⌝ ·ᶜ wkConₘ ρ (𝟘ᶜ ∙ 𝟙) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)               ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
        (p · ⌜ m ᵐ· p ⌝) ·ᶜ wkConₘ ρ (𝟘ᶜ ∙ 𝟙) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)              ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (·⌜ᵐ·⌝ m)) ⟩
        (p · ⌜ m ⌝) ·ᶜ wkConₘ ρ (𝟘ᶜ ∙ 𝟙) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)                   ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm m)) ⟩
        (⌜ m ⌝ · p) ·ᶜ wkConₘ ρ (𝟘ᶜ ∙ 𝟙) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)                   ≈⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
        ⌜ m ⌝ ·ᶜ p ·ᶜ wkConₘ ρ (𝟘ᶜ ∙ 𝟙) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)                    ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
        ⌜ m ⌝ ·ᶜ wkConₘ ρ (p ·ᶜ (𝟘ᶜ ∙ 𝟙)) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)                  ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _))) ⟩
        ⌜ m ⌝ ·ᶜ wkConₘ ρ (𝟘ᶜ ∙ p) +ᶜ ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ 𝟘)                         ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
        ⌜ m ⌝ ·ᶜ (wkConₘ ρ (𝟘ᶜ ∙ p) +ᶜ wkConₘ ρ (γ ∙ 𝟘))                                ≈˘⟨ ·ᶜ-congˡ (wk-+ᶜ ρ) ⟩
        ⌜ m ⌝ ·ᶜ (wkConₘ ρ ((𝟘ᶜ ∙ p) +ᶜ (γ ∙ 𝟘)))                                       ≈⟨ ·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-identityˡ _ ∙ +-identityʳ _)) ⟩
        ⌜ m ⌝ ·ᶜ wkConₘ ρ (γ ∙ p) ∎
      where
      open ≤ᶜ-reasoning

  opaque

    -- A usage inversion lemma for sink γ.

    inv-usage-sink : δ ▸[ m ] sink γ → δ ≤ᶜ ⌜ m ⌝ ·ᶜ γ
    inv-usage-sink ▸γ =
      inv-usage-sink-wk (PE.subst (_▸[_]_ _ _) (PE.sym (wk-id _)) ▸γ)

  opaque

    -- A usage inversion lemma for sink γ at mode 𝟙ᵐ.
    -- Note that γ is an upper bound on valid usage contexts for sink γ
    -- and is thus the greatest valid context.

    inv-usage-sink-𝟙ᵐ : δ ▸[ 𝟙ᵐ ] sink γ → δ ≤ᶜ γ
    inv-usage-sink-𝟙ᵐ ▸γ =
      ≤ᶜ-trans (inv-usage-sink ▸γ) (≤ᶜ-reflexive (·ᶜ-identityˡ _))

  opaque

    -- A usage inversion lemma for sink γ at mode 𝟘ᵐ.

    inv-usage-sink-𝟘ᵐ : ∀ {ok} → δ ▸[ 𝟘ᵐ[ ok ] ] sink γ → δ ≤ᶜ 𝟘ᶜ
    inv-usage-sink-𝟘ᵐ ▸γ =
      ≤ᶜ-trans (inv-usage-sink ▸γ) (≤ᶜ-reflexive (·ᶜ-zeroˡ _))

------------------------------------------------------------------------
-- Usage properties that hold for "arbitrary" usage relations with a
-- certain anstaz for the natrec rule (and some type restrictions).

module Natrec₁
  (usage-relation-natrec : Usage-relation-natrec₁)
  -- Weak unit types are allowed
  (Unit-ok : Unitʷ-allowed)
  -- Certain Σ-types are allowed
  (Σ-ok : ∀ {r} → Σʷ-allowed r 𝟘)
  where

  open Usage-relation-natrec₁ usage-relation-natrec
  open Usage usage-relation

  private

    opaque
      unfolding Sink-allowed

      -- The Sink type is allowed.

      Sink-ok : Sink-allowed γ
      Sink-ok {γ = ε} = Unit-ok
      Sink-ok {γ = γ ∙ p} = Sink-ok {γ = γ} , Σ-ok

    opaque

      -- A term used in the proofs below.

      Z : Conₘ n → Term n
      Z γ = Sink Δᴺ γ

    opaque
      unfolding Z

      Z₀≡ : wk1 (Z γ) [ zero ]₀ PE.≡ Sink Δᴺ γ
      Z₀≡ = wk1-sgSubst _ _

    opaque
      unfolding Z

      Z₊≡ : wk1 (Z γ) [ suc (var x1) ]↑² PE.≡ wk₂ (Sink Δᴺ γ)
      Z₊≡ {γ} = begin
        wk1 (Z γ) [ suc (var x1) ]↑²       ≡⟨⟩
        wk1 (Sink Δᴺ γ) [ suc (var x1) ]↑² ≡⟨ wk1-tail (Sink Δᴺ γ) ⟩
        Sink Δᴺ γ [ wkSubst 2 idSubst ]    ≡˘⟨ wk≡subst _ _ ⟩
        wk₂ (Sink Δᴺ γ)                    ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding Z

      ⊢Z : Γᴺ ⊢ Z γ ∷ U 0
      ⊢Z = ⊢∷-Sink-Γᴺ Sink-ok

    opaque
      unfolding Z

      ▸Z : 𝟘ᶜ ▸[ 𝟙ᵐ ] Z γ
      ▸Z = ▸Sink-Δᴺ

    opaque

      -- A term used in the proofs below.

      S : (p r : M) → Conₘ n → Term (3+ n)
      S p r δ = Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 5 ]′ (Sink Δᴺ δ))

    opaque

      S≡-lemma : {σ : Subst n _} → wk[ 5 ]′ t [ σ ⇑[ 4 ] ] PE.≡ wk[ 4 ]′ (wk1 t [ σ ])
      S≡-lemma {t} {σ} = begin
        wk[ 5 ]′ t [ σ ⇑[ 4 ] ]      ≡˘⟨ PE.cong (_[ σ ⇑[ 4 ] ]) (wk[]≡wk[]′ {t = t}) ⟩
        wk[ 5 ] t [ σ ⇑[ 4 ] ]       ≡⟨⟩
        wk[ 4 ] (wk1 t) [ σ ⇑[ 4 ] ] ≡⟨ wk[]-⇑[] {t = wk1 t} 4 ⟩
        wk[ 4 ] (wk1 t [ σ ])        ≡⟨ wk[]≡wk[]′ ⟩
        wk[ 4 ]′ (wk1 t [ σ ])       ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding S

      S₀≡ : S p r δ [ sgSubst t ⇑[ 2 ] ] PE.≡ Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 4 ]′ (Sink Δᴺ δ))
      S₀≡ {p} {r} {δ} {t} = PE.cong (λ x → Σʷ r , 𝟘 ▷ _ ▹ (Σʷ p , 𝟘 ▷ _ ▹ x)) $ begin
        wk[ 5 ]′ (Sink Δᴺ δ) [ sgSubst t ⇑[ 4 ] ] ≡⟨ S≡-lemma {t = Sink Δᴺ δ} ⟩
        wk[ 4 ]′ (wk1 (Sink Δᴺ δ) [ sgSubst t ])  ≡⟨ PE.cong wk[ 4 ]′ (wk1-sgSubst _ _) ⟩
        wk[ 4 ]′ (Sink Δᴺ δ)                      ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding S

      S₊≡ :
        S p r δ [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ⇑[ 2 ] ] PE.≡
        Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ))
      S₊≡ {p} {r} {δ} = PE.cong (λ x → Σʷ r , 𝟘 ▷ _ ▹ (Σʷ p , 𝟘 ▷ _ ▹ x)) $ begin
        wk[ 5 ]′ (Sink Δᴺ δ) [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ⇑[ 4 ] ] ≡⟨ S≡-lemma {t = Sink Δᴺ δ} ⟩
        wk[ 4 ]′ (wk1 (Sink Δᴺ δ) [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ])  ≡⟨ PE.cong wk[ 4 ]′ (wk1-tail (Sink Δᴺ δ)) ⟩
        wk[ 4 ]′ (Sink Δᴺ δ [ wkSubst 2 idSubst ])                                   ≡˘⟨ PE.cong wk[ 4 ]′ (wk≡subst (step (step id)) _) ⟩
        wk[ 4 ]′ (wk[ 2 ]′ (Sink Δᴺ δ))                                              ≡⟨ wk-comp _ _ _ ⟩
        wk[ 6 ]′ (Sink Δᴺ δ)                                                         ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding S

      ⊢S : Γᴺ »∙ U l ⊢ S p r δ ∷ U l
      ⊢S =
        let ⊢x0 = var₀ (Uⱼ ⊢Γᴺ)
        in  ΠΣⱼ ⊢x0
             (ΠΣⱼ (ℕⱼ (∙ univ ⊢x0))
               (wkTerm (stepʷ (step (step (step (step id)))) (ℕⱼ (∙ (univ ⊢x0))))
                 (⊢∷-Sink-Γᴺ Sink-ok))
               Σ-ok)
             Σ-ok

    opaque

      ⊢S₀ : Γᴺ »∙ U l ⊢ Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 4 ]′ (Sink Δᴺ δ)) ∷ U l
      ⊢S₀ {l} =
        PE.subst (Γᴺ »∙ U l ⊢_∷ U l) S₀≡
          (subst-⊢∷-⇑ {k = 2} ⊢S (⊢ˢʷ∷-sgSubst (zeroⱼ ⊢Γᴺ)))

    opaque

      ⊢S₊ : Γᴺ ⊢ A → Γᴺ »∙ A »∙ ℕ »∙ U l ⊢ Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ)) ∷ U l
      ⊢S₊ {A} {l} ⊢A =
        PE.subst (Γᴺ »∙ A »∙ ℕ »∙ U l ⊢_∷ _) S₊≡
          (subst-⊢∷-⇑ {k = 2} ⊢S (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst (∙ ⊢A) (⊢ˢʷ∷-idSubst ⊢Γᴺ))
            (sucⱼ (var₁ ⊢A))))

    opaque
      unfolding S

      ▸S : 𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · ⌜ ⌞ r ⌟ ⌝ ▸[ 𝟙ᵐ ] S p r δ
      ▸S {r} {p} {δ} =
        let ▸δ = sub (wkUsage ▸Sink-Δᴺ) $ begin
              𝟘ᶜ ∙ 𝟙 · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ ∙ 𝟘 ∎
            open ≤ᶜ-reasoning
            ▸Σ = sub (Σʷₘ ℕₘ ▸δ) $ begin
              𝟘ᶜ ∙ 𝟙 · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ         ≈˘⟨ +ᶜ-identityʳ _ ⟩
              𝟘ᶜ +ᶜ 𝟘ᶜ   ∎
        in  sub (Σʷₘ varₘ ▸Σ) $ begin
          𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · ⌜ ⌞ r ⌟ ⌝  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityˡ _ ⟩
          𝟘ᶜ ∙ 𝟘     ∙ ⌜ ⌞ r ⌟ ⌝      ≈˘⟨ +ᶜ-identityʳ _ ⟩
          (𝟘ᶜ , x0 ≔ ⌜ ⌞ r ⌟ ⌝) +ᶜ 𝟘ᶜ ∎
        where
        open ≤ᶜ-reasoning

    opaque

      -- A term used in the proofs below.

      α : (p r : M) (γ δ : Conₘ n) → Term (1+ n)
      α p r γ δ = natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) (wk1 (Z γ)) (S p r δ) (var x0)

    opaque
      unfolding α

      α₀≡ :
        α p r γ δ [ zero ]₀ PE.≡
        natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) (Sink Δᴺ γ)
          (Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 4 ]′ (Sink Δᴺ δ))) zero
      α₀≡ {p} {r} {γ} {δ} =
        PE.cong₂ (λ x y → natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) x y zero)
          Z₀≡ S₀≡

    opaque
      unfolding α

      α₊≡ :
        α p r γ δ [ suc (var x1) ]↑² PE.≡
        natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) (wk₂ (Sink Δᴺ γ))
          (Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ))) (suc (var x1))
      α₊≡ {r} =
        PE.cong₂ (λ x y → natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) x y (suc (var x1))) Z₊≡ S₊≡

    opaque
      unfolding α Z S

      wk1α≡ :
        wk1 (α p r γ δ) PE.≡
        natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) (wk₂ (Sink Δᴺ γ))
          (Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ)))
          (var x1)
      wk1α≡ {r} =
        PE.cong₂ (λ z s → natrec 𝟘 𝟘 ⌜ ⌞ r ⌟ ⌝ (U 0) z s (var x1))
          (wk-comp _ _ _)
          (PE.cong (λ x → Σʷ r , 𝟘 ▷ _ ▹ (Σʷ _ , 𝟘 ▷ _ ▹ x)) (wk-comp _ _ _))

    opaque
      unfolding α

      ⊢α : Γᴺ ⊢ α p r γ δ
      ⊢α = univ (natrecⱼ (wkTerm (stepʷ id (ℕⱼ ⊢Γᴺ)) ⊢Z) ⊢S (var ⊢Γᴺ here))

    opaque
      unfolding α

      ▸¹α : tailₘ (g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ) ∙ f 𝟘 ⌜ ⌞ r ⌟ ⌝ + headₘ {n = n} (g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ) ▸[ 𝟙ᵐ ] α {n = n} p r γ δ
      ▸¹α {r} {p} =
        let ▸U = sub Uₘ (≤ᶜ-refl {γ = 𝟘ᶜ} ∙ ≤-reflexive (·-zeroʳ _))
            η = g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ
            open ≤ᶜ-reasoning
        in  sub (natrecₘ (wkUsage ▸Z) ▸S varₘ ▸U) $ begin
          tailₘ η ∙ f 𝟘 ⌜ ⌞ r ⌟ ⌝ + headₘ η                ≈˘⟨ +ᶜ-identityˡ _ ∙ PE.refl ⟩
          (𝟘ᶜ ∙ f 𝟘 ⌜ ⌞ r ⌟ ⌝) +ᶜ (tailₘ η ∙ headₘ η)      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) ⟩
          f 𝟘 ⌜ ⌞ r ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ (tailₘ η ∙ headₘ η) ≡⟨ PE.cong (f 𝟘 ⌜ ⌞ r ⌟ ⌝ ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ_) (headₘ-tailₘ-correct η) ⟩
          f 𝟘 ⌜ ⌞ r ⌟ ⌝ ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙) +ᶜ η              ∎

    opaque

      ▸α : ⌜ m ⌝ ·ᶜ (tailₘ (g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ) ∙ f 𝟘 ⌜ ⌞ r ⌟ ⌝ + headₘ {n = n} (g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ)) ▸[ m ] α {n = n} p r γ δ
      ▸α {m = 𝟘ᵐ} = sub (▸-𝟘 ▸¹α) (≤ᶜ-reflexive (·ᶜ-zeroˡ _))
      ▸α {m = 𝟙ᵐ} = sub ▸¹α (≤ᶜ-reflexive (·ᶜ-identityˡ _))

    opaque

      -- A term used in the proofs below.

      ζ : Conₘ n → Term n
      ζ γ = sink γ

    opaque
      unfolding ζ

      ⊢ζ : Γᴺ ⊢ ζ γ ∷ α p r γ δ [ zero ]₀
      ⊢ζ = conv (⊢∷-sink ⊢Γᴺ Sink-ok)
             (⊢≡-congˡ (sym (univ (natrec-zero (⊢∷-Sink-Γᴺ Sink-ok) ⊢S₀))) (PE.sym α₀≡))

    opaque
      unfolding ζ

      ▸ζ : γ ▸[ 𝟙ᵐ ] ζ γ
      ▸ζ = ▸sink _

    opaque
      unfolding ζ

      inv-usage-ζ : γ ▸[ m ] ζ δ → γ ≤ᶜ ⌜ m ⌝ ·ᶜ δ
      inv-usage-ζ = inv-usage-sink

    opaque

      -- A term used in the proofs below.

      σ : (p r : M) → Conₘ n → Term (2+ n)
      σ p r δ = prodʷ r (var x0) (prodʷ p (var x1) (wk₂ (sink δ)))

    opaque
      unfolding σ

      ⊢σ : Γᴺ »∙ α p r γ δ ⊢ σ p r δ ∷ α p r γ δ [ suc (var x1) ]↑²
      ⊢σ {p} {r} {γ} {δ} =
        let ⊢α′ = ⊢α {p = p} {r = r} {γ = γ} {δ = δ}
            ⊢δ = wkTerm (stepʷ (step id) ⊢α′) (⊢∷-sink ⊢Γᴺ Sink-ok)
            ⊢δ′ = ⊢∷-conv-PE ⊢δ (PE.sym (step-sgSubst (Sink Δᴺ _) (var x1)))
            ⊢Sink = W.wk (stepʷ (step (step (step id))) (ℕⱼ (∙ W.wk (stepʷ id ⊢α′) ⊢α′)))
                      (⊢-Sink ⊢Γᴺ Sink-ok)
            ⊢Sink′ = W.wk (stepʷ (step (step id)) (ℕⱼ (∙ ⊢α′)))
                       (⊢-Sink ⊢Γᴺ Sink-ok)
            ⊢Z₊ = wkTerm (stepʷ (step id) ⊢α′) (⊢∷-Sink-Γᴺ Sink-ok)
            ⊢Σ = ΠΣⱼ ⊢Sink Σ-ok
            ⊢t = ⊢∷-conv-PE (prodⱼ ⊢Sink′ (var₁ ⊢α′) ⊢δ′ Σ-ok)
                   (PE.cong (Σ p , 𝟘 ▷ ℕ ▹_) lemma′)
            open TEq
        in  conv (prodⱼ ⊢Σ (var₀ ⊢α′) ⊢t Σ-ok)
          (Σʷ r , 𝟘 ▷ wk1 (α p r γ δ) ▹ Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 4 ]′ (Sink Δᴺ δ)
            ≡⟨ PE.cong₂ (λ x y → Σʷ r , 𝟘 ▷ x ▹ Σʷ p , 𝟘 ▷ ℕ ▹ y) wk1α≡ lemma ⟩⊢≡
          Σʷ r , 𝟘 ▷ _ ▹ Σʷ p , 𝟘 ▷ ℕ ▹ _
            ≡˘⟨ univ (natrec-suc ⊢Z₊ (⊢S₊ ⊢α′) (var₁ ⊢α′))  ⟩⊢∎≡
          natrec 𝟘 𝟘 _ (U 0) (wk₂ (Sink Δᴺ γ))
            (Σʷ r , 𝟘 ▷ var x0 ▹ Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ)) (suc (var x1))
              ≡˘⟨ α₊≡ ⟩
          α p r γ δ [ suc (var x1) ]↑² ∎)
        where
        open Tools.Reasoning.PropositionalEquality
        lemma′ : wk[ 3 ]′ t PE.≡ wk[ 4 ]′ t [ sgSubst u ⇑ ]
        lemma′ {t} {u} = begin
           wk[ 3 ]′ t                 ≡˘⟨ wk[]≡wk[]′ ⟩
           wk[ 3 ] t                  ≡˘⟨ PE.cong wk1 (wk1-sgSubst _ _) ⟩
           wk1 (wk[ 3 ] t [ u ]₀)     ≡˘⟨ wk[]-⇑[] {t = wk[ 3 ] t} 1 ⟩
           wk[ 4 ] t [ sgSubst u ⇑ ]  ≡⟨ PE.cong (_[ sgSubst u ⇑ ]) (wk[]≡wk[]′ {k = 4} {t = t}) ⟩
           wk[ 4 ]′ t [ sgSubst u ⇑ ] ∎
        lemma : wk[ 4 ]′ t PE.≡ wk[ 6 ]′ t [ consSubst (sgSubst u) v ⇑[ 2 ] ]
        lemma {t} {u} {v} = begin
          wk[ 4 ]′ t                                     ≡˘⟨ wk[]≡wk[]′ ⟩
          wk[ 4 ] t                                      ≡˘⟨ PE.cong wk2 wk2-[,] ⟩
         wk2 (wk[ 4 ] t [ consSubst (sgSubst u) v ])     ≡˘⟨ wk[]-⇑[] {t = wk[ 4 ] t} 2 ⟩
          wk[ 6 ] t [ consSubst (sgSubst u) v ⇑[ 2 ] ]   ≡⟨ PE.cong (_[ consSubst (sgSubst u) v ⇑[ 2 ] ]) (wk[]≡wk[]′ {k = 6} {t = t}) ⟩
          wk[ 6 ]′ t [ consSubst (sgSubst u) v ⇑[ 2 ] ]  ∎

    opaque
      unfolding σ

      ▸σ : δ ∙ ⌜ 𝟙ᵐ ⌝ · p ∙ ⌜ 𝟙ᵐ ⌝ · r ▸[ 𝟙ᵐ ] σ p r δ
      ▸σ {δ} {p} {r} =
        sub (prodʷₘ varₘ (prodʷₘ varₘ (wkUsage (▸sink δ)))) $ begin
        δ                        ∙ 𝟙 · p                     ∙ 𝟙 · r                     ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ∙ ·-identityˡ _ ⟩
        δ                        ∙ p                         ∙ r                         ≈˘⟨ ≈ᶜ-refl ∙ ·⌜⌞⌟⌝ ∙ ·⌜⌞⌟⌝  ⟩
        δ                        ∙ p · ⌜ ⌞ p ⌟ ⌝             ∙ r · ⌜ ⌞ r ⌟ ⌝             ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ⟩
        𝟘ᶜ +ᶜ δ                  ∙ 𝟘 + p · ⌜ ⌞ p ⌟ ⌝         ∙ r · ⌜ ⌞ r ⌟ ⌝ + 𝟘         ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (+ᶜ-identityˡ _) ∙
                                                                                             +-cong (·-zeroʳ _) (+-identityʳ _) ∙
                                                                                             +-congˡ (+-identityʳ _) ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ δ       ∙ r · 𝟘 + p · ⌜ ⌞ p ⌟ ⌝ + 𝟘 ∙ r · ⌜ ⌞ r ⌟ ⌝ + 𝟘 + 𝟘     ≈˘⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _)) ∙ PE.refl ∙
                                                                                             +-congˡ (+-congʳ (·-zeroʳ _)) ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ δ  ∙ r · 𝟘 + p · ⌜ ⌞ p ⌟ ⌝ + 𝟘 ∙ r · ⌜ ⌞ r ⌟ ⌝ + p · 𝟘 + 𝟘 ≡⟨⟩
        r ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ r ⌟ ⌝) +ᶜ p ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘) ∎
        where
        open ≤ᶜ-reasoning

    opaque
      unfolding σ

      inv-usage-σ : γ ▸[ m ] σ p r δ → γ ≤ᶜ ⌜ m ⌝ ·ᶜ (δ ∙ p ∙ r)
      inv-usage-σ {γ} {m} {p} {r} {δ} ▸σ =
        let γ₁ , γ₂ , ▸x0 , ▸t , γ≤ = inv-usage-prodʷ ▸σ
            γ₃ , γ₄ , ▸x1 , ▸δ , γ₂≤ = inv-usage-prodʷ ▸t
        in  begin
          γ                                                                            ≤⟨ γ≤ ⟩
          r ·ᶜ γ₁ +ᶜ γ₂                                                                ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var ▸x0)) γ₂≤ ⟩
          r ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r ⌝) +ᶜ p ·ᶜ γ₃ +ᶜ γ₄                                      ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var ▸x1))
                                                                                          (inv-usage-sink-wk ▸δ)) ⟩
          r ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· r ⌝) +ᶜ p ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· p ⌝ ∙ 𝟘) +ᶜ ⌜ m ⌝ ·ᶜ (δ ∙ 𝟘 ∙ 𝟘) ≈⟨ +ᶜ-cong
                                                                                           (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m)
                                                                                           (+ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ m ∙ ·-zeroʳ _)) ⟩
          (𝟘ᶜ ∙ r · ⌜ m ⌝) +ᶜ (𝟘ᶜ ∙ p · ⌜ m ⌝ ∙ 𝟘) +ᶜ ⌜ m ⌝ ·ᶜ (δ ∙ 𝟘 ∙ 𝟘)             ≈˘⟨ +ᶜ-cong
                                                                                            (·ᶜ-zeroʳ _ ∙ ⌜⌝-·-comm m)
                                                                                            (+ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ⌜⌝-·-comm m ∙ ·-zeroʳ _)) ⟩
          ⌜ m ⌝ ·ᶜ (𝟘ᶜ ∙ r) +ᶜ ⌜ m ⌝ ·ᶜ (𝟘ᶜ ∙ p ∙ 𝟘) +ᶜ ⌜ m ⌝ ·ᶜ (δ ∙ 𝟘 ∙ 𝟘)           ≈˘⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          ⌜ m ⌝ ·ᶜ (𝟘ᶜ ∙ r) +ᶜ ⌜ m ⌝ ·ᶜ ((𝟘ᶜ ∙ p ∙ 𝟘) +ᶜ (δ ∙ 𝟘 ∙ 𝟘))                  ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _)) ⟩
          ⌜ m ⌝ ·ᶜ (𝟘ᶜ ∙ r) +ᶜ ⌜ m ⌝ ·ᶜ (δ ∙ p ∙ 𝟘)                                    ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m ⌝ ·ᶜ ((𝟘ᶜ ∙ r) +ᶜ (δ ∙ p ∙ 𝟘))                                           ≈⟨ ·ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _) ⟩
          ⌜ m ⌝ ·ᶜ (δ ∙ p ∙ r)                                                         ∎
        where
        open ≤ᶜ-reasoning

    opaque

      -- A term used in the proofs below.

      τ : (p r : M) (γ δ : Conₘ n) → Nat → Term n
      τ {n} p r γ δ i =
        natrec p (f 𝟘 ⌜ ⌞ r ⌟ ⌝ + headₘ {n = n} (g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ)) r
          (α p r γ δ) (ζ γ) (σ p r δ) (sucᵏ i)

    opaque
      unfolding τ

      -- The term τ p r γ δ i is well-resourced under context g p r γ δ.

      ▸τ : g p r γ δ ▸[ 𝟙ᵐ ] τ p r γ δ i
      ▸τ {p} {r} {γ} {δ} {i} =
        sub (natrecₘ ▸ζ ▸σ (▸sucᵏ i) ▸α) $ begin
          g p r γ δ                ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ g p r γ δ          ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          f p r ·ᶜ 𝟘ᶜ +ᶜ g p r γ δ ∎
        where
        open ≤ᶜ-reasoning

    opaque
      unfolding τ

      inv-usage-τ :
        η ▸[ m ] τ p r γ δ i →
        ∃₂ λ η₁ η₂ → η₁ ≤ᶜ ⌜ m ⌝ ·ᶜ γ × η₂ ≤ᶜ ⌜ m ⌝ ·ᶜ δ × η ≤ᶜ g p r η₁ η₂
      inv-usage-τ {η} {m} {p} {r} {γ} {δ} ▸τ =
        let η₁ , η₂ , η₃ , η₄ , ▸ζ , ▸σ , ▸i , ▸α , η≤ = inv-usage-natrec ▸τ
        in  _ , _
              , (begin
                  η₁         ≤⟨ inv-usage-ζ ▸ζ ⟩
                  ⌜ m ⌝ ·ᶜ γ ∎)
              , (begin
                  η₂         ≤⟨ tailₘ-monotone (tailₘ-monotone (inv-usage-σ ▸σ)) ⟩
                  ⌜ m ⌝ ·ᶜ δ ∎)
              , (begin
                  η                          ≤⟨ η≤ ⟩
                  f p r ·ᶜ η₃ +ᶜ g p r η₁ η₂ ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-sucᵏ ▸i)) ⟩
                  f p r ·ᶜ 𝟘ᶜ +ᶜ g p r η₁ η₂ ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
                  𝟘ᶜ +ᶜ g p r η₁ η₂          ≈⟨ +ᶜ-identityˡ _ ⟩
                  g p r η₁ η₂                ∎)
        where
        open ≤ᶜ-reasoning

    opaque
      unfolding σ

      inv-usage-σ[,] :
        η ▸[ 𝟙ᵐ ] σ p r δ [ t , u ]₁₀ →
        ∃₂ λ η₁ η₂ → η₁ ▸[ ⌞ p ⌟ ] t × η₂ ▸[ ⌞ r ⌟ ] u × η ≤ᶜ r ·ᶜ η₂ +ᶜ p ·ᶜ η₁ +ᶜ δ
      inv-usage-σ[,] {η} {p} {r} {δ} ▸σ =
        let η₁ , η₂ , ▸u , ▸v , η≤ = inv-usage-prodʷ ▸σ
            η₃ , η₄ , ▸t , ▸δ , η₂≤ = inv-usage-prodʷ ▸v
            ▸δ′ = PE.subst (λ x → η₄ ▸[ 𝟙ᵐ ] x) (wk₂-[,] {t = sink δ}) ▸δ
            open ≤ᶜ-reasoning
        in  _ , _ , ▸t , ▸u , (begin
          η                        ≤⟨ η≤ ⟩
          r ·ᶜ η₁ +ᶜ η₂            ≤⟨ +ᶜ-monotoneʳ η₂≤ ⟩
          r ·ᶜ η₁ +ᶜ p ·ᶜ η₃ +ᶜ η₄ ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (inv-usage-sink-𝟙ᵐ ▸δ′)) ⟩
          r ·ᶜ η₁ +ᶜ p ·ᶜ η₃ +ᶜ δ  ∎)

    opaque
      unfolding σ

      inv-usage-σ[k,τ] :
        η ▸[ 𝟙ᵐ ] σ p r δ [ sucᵏ i , τ p r γ δ i ]₁₀ →
        ∃ λ θ → θ ▸[ ⌞ r ⌟ ] τ p r γ δ i × η ≤ᶜ δ +ᶜ r ·ᶜ θ
      inv-usage-σ[k,τ] {η} {p} {r} {δ} ▸σ =
        let η₁ , η₂ , ▸i , ▸τ , η≤ = inv-usage-σ[,] ▸σ
            open ≤ᶜ-reasoning
        in  _ , ▸τ , (begin
          η                      ≤⟨ η≤ ⟩
          r ·ᶜ η₂ +ᶜ p ·ᶜ η₁ +ᶜ δ ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-sucᵏ ▸i))) ⟩
          r ·ᶜ η₂ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ δ ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _)) ⟩
          r ·ᶜ η₂ +ᶜ 𝟘ᶜ +ᶜ δ      ≈⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
          r ·ᶜ η₂ +ᶜ δ            ≈⟨ +ᶜ-comm _ _ ⟩
          δ +ᶜ r ·ᶜ η₂            ∎)

    opaque
      unfolding τ

      -- The context nrᵢᶜ r γ δ i is an upper bound on valid contexts
      -- for the term τ p r γ δ i.

      ≤-nrᵢᶜ : ∀ i → η ▸[ 𝟙ᵐ ] τ p r γ δ i → η ≤ᶜ nrᵢᶜ r γ δ i
      ≤-nrᵢᶜ {η} {r} {γ} {δ} 0 ▸nr =
        let open ≤ᶜ-reasoning in begin
          η            ≤⟨ inv-usage-ζ (usagePresTerm (λ ()) ▸nr (natrec-zero ⊢ζ ⊢σ)) ⟩
          𝟙 ·ᶜ γ       ≈⟨ ·ᶜ-identityˡ _ ⟩
          γ            ≈˘⟨ nrᵢᶜ-zero ⟩
          nrᵢᶜ r γ δ 0 ∎
      ≤-nrᵢᶜ {η} {p} {r} {γ} {δ} (1+ i) ▸nr =
        let ▸s = usagePresTerm (λ ()) ▸nr (natrec-suc ⊢ζ ⊢σ (⊢sucᵏ ⊢Γᴺ))
            θ , ▸IH , η≤ = inv-usage-σ[k,τ] ▸s
            open ≤ᶜ-reasoning
        in  case is-𝟘? r of λ where
          (yes PE.refl) → begin
            η                      ≤⟨ η≤ ⟩
            δ +ᶜ 𝟘 ·ᶜ θ            ≈⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
            δ +ᶜ 𝟘ᶜ                ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
            δ +ᶜ 𝟘 ·ᶜ nrᵢᶜ 𝟘 γ δ i ≈˘⟨ nrᵢᶜ-suc ⟩
            nrᵢᶜ 𝟘 γ δ (1+ i)      ∎
          (no r≢𝟘) → begin
            η                      ≤⟨ η≤ ⟩
            δ +ᶜ r ·ᶜ θ            ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ
                                       (≤-nrᵢᶜ i (PE.subst (θ ▸[_] τ p r γ δ i)
                                         (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸IH))) ⟩
            δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ i ≈˘⟨ nrᵢᶜ-suc ⟩
            nrᵢᶜ r γ δ (1+ i)      ∎

  opaque

    -- The context g p r γ δ is bounded from above by nrᵢᶜ r γ δ i for all i.
    -- That is, g p r γ δ is smaller than γ, δ +ᶜ r ·ᶜ γ, ….

    g-≤-nrᵢᶜ : ∀ i → g p r γ δ ≤ᶜ nrᵢᶜ r γ δ i
    g-≤-nrᵢᶜ i = ≤-nrᵢᶜ i ▸τ

  opaque

    -- If mode 𝟘ᵐ is allowed then g p r 𝟘ᶜ 𝟘ᶜ is equal to 𝟘ᶜ.

    g𝟘𝟘≈𝟘 : T 𝟘ᵐ-allowed → g p r 𝟘ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
    g𝟘𝟘≈𝟘 {p} {r} {n} ok =
      let 𝟘▸τ = ▸-𝟘 {ok = ok} (▸τ {p = p} {r = r} {γ = 𝟘ᶜ {n = n}} {δ = 𝟘ᶜ} {i = 0})
          γ , δ , γ≤ , δ≤ , 𝟘≤g = inv-usage-τ 𝟘▸τ
          γ≤𝟘 = begin
            γ       ≤⟨ γ≤ ⟩
            𝟘 ·ᶜ 𝟘ᶜ ≈⟨ ·ᶜ-zeroʳ _ ⟩
            𝟘ᶜ      ∎
          𝟘≤γ = begin
            𝟘ᶜ           ≤⟨ 𝟘≤g ⟩
            g p r γ δ    ≤⟨ g-≤-nrᵢᶜ 0 ⟩
            nrᵢᶜ r γ δ 0 ≈⟨ nrᵢᶜ-zero ⟩
            γ ∎
          γ≈𝟘 = ≤ᶜ-antisym γ≤𝟘 𝟘≤γ
          δ≤𝟘 = begin
            δ ≤⟨ δ≤ ⟩
            𝟘 ·ᶜ 𝟘ᶜ ≈⟨ ·ᶜ-zeroʳ _ ⟩
            𝟘ᶜ ∎
          𝟘≤δ = begin
            𝟘ᶜ                     ≤⟨ 𝟘≤g ⟩
            g p r γ δ              ≤⟨ g-≤-nrᵢᶜ 1 ⟩
            nrᵢᶜ r γ δ 1           ≈⟨ nrᵢᶜ-suc ⟩
            δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ 0 ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ nrᵢᶜ-zero) ⟩
            δ +ᶜ r ·ᶜ γ            ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ γ≈𝟘) ⟩
            δ +ᶜ r ·ᶜ 𝟘ᶜ          ≈⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
            δ +ᶜ 𝟘ᶜ               ≈⟨ +ᶜ-identityʳ _ ⟩
            δ ∎
          δ≈𝟘 = ≤ᶜ-antisym δ≤𝟘 𝟘≤δ
          g≤𝟘 = begin
            g p r 𝟘ᶜ 𝟘ᶜ    ≤⟨ g-≤-nrᵢᶜ 0 ⟩
            nrᵢᶜ r 𝟘ᶜ 𝟘ᶜ 0 ≈⟨ nrᵢᶜ-zero ⟩
            𝟘ᶜ             ∎
          𝟘≤g′ = begin
            𝟘ᶜ          ≤⟨ 𝟘≤g ⟩
            g p r γ δ   ≡⟨ PE.cong₂ (g p r) (≈ᶜ→≡ γ≈𝟘) (≈ᶜ→≡ δ≈𝟘) ⟩
            g p r 𝟘ᶜ 𝟘ᶜ ∎
      in  ≤ᶜ-antisym g≤𝟘 𝟘≤g′
      where
      open ≤ᶜ-reasoning

    private

      opaque

        -- A term used in some lemmas below.

        τ′ : (p r : M) (t : Term 1) → Term 1
        τ′ p r t = natrec p (f 𝟘 ⌜ ⌞ r ⌟ ⌝ + headₘ {n = 1} (g 𝟘 ⌜ ⌞ r ⌟ ⌝ 𝟘ᶜ 𝟘ᶜ)) r (α p r 𝟘ᶜ 𝟘ᶜ) (ζ 𝟘ᶜ) (σ p r 𝟘ᶜ) t

      opaque
        unfolding τ′

        ▸τ′ : T 𝟘ᵐ-allowed → ε ∙ f p r ▸[ 𝟙ᵐ ] τ′ p r (suc (var x0))
        ▸τ′ {p} {r} ok = sub (natrecₘ ▸ζ ▸σ (sucₘ varₘ) ▸α) $ begin
          ε ∙ f p r                       ≈˘⟨ +ᶜ-identityʳ _ ⟩
          (ε ∙ f p r) +ᶜ 𝟘ᶜ               ≈˘⟨ +ᶜ-cong (ε ∙ ·-identityʳ _) (g𝟘𝟘≈𝟘 ok) ⟩
          f p r ·ᶜ (ε ∙ 𝟙) +ᶜ g p r 𝟘ᶜ 𝟘ᶜ ∎
          where
          open ≤ᶜ-reasoning

      opaque
        unfolding τ′

        -- The context ε ∙ p + r · f p r is an upper bound of valid contexts for
        -- τ′ p r (suc (var x0)).

        ≤-p+rf : γ ▸[ 𝟙ᵐ ] τ′ p r (suc (var x0)) → γ ≤ᶜ (ε ∙ p + r · f p r)
        ≤-p+rf {γ} {p} {r} ▸nr =
          let ▸s = usagePresTerm (λ ()) ▸nr (natrec-suc ⊢ζ ⊢σ (var₀ (ℕⱼ εε)))
              γ₁ , γ₂ , ▸x0 , ▸nr′ , γ≤ = inv-usage-σ[,] ▸s
              δ₁ , δ₂ , δ₃ , _ , ▸ζ , _ , ▸x0′ , _ , γ₂≤ = inv-usage-natrec ▸nr′
              open ≤ᶜ-reasoning
          in  begin
            γ                                                                         ≤⟨ γ≤ ⟩
            r ·ᶜ γ₂ +ᶜ p ·ᶜ γ₁ +ᶜ 𝟘ᶜ                                                  ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
            r ·ᶜ γ₂ +ᶜ p ·ᶜ γ₁                                                        ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ γ₂≤) (·ᶜ-monotoneʳ (inv-usage-var ▸x0)) ⟩
            r ·ᶜ (f p r ·ᶜ δ₃ +ᶜ g p r δ₁ δ₂) +ᶜ p ·ᶜ (ε ∙ ⌜ ⌞ p ⌟ ⌝)                 ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var ▸x0′)) (g-≤-nrᵢᶜ 0))) ⟩
            r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ nrᵢᶜ r δ₁ δ₂ 0) +ᶜ p ·ᶜ (ε ∙ ⌜ ⌞ p ⌟ ⌝) ≈⟨ +ᶜ-cong (·ᶜ-congˡ (+ᶜ-congˡ nrᵢᶜ-zero)) (ε ∙ ·⌜⌞⌟⌝) ⟩
            r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ δ₁) +ᶜ (ε ∙ p)                         ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (inv-usage-ζ ▸ζ))) ⟩
            r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ ⌜ ⌞ r ⌟ ⌝ ·ᶜ 𝟘ᶜ) +ᶜ (ε ∙ p)            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _))) ⟩
            r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ 𝟘ᶜ) +ᶜ (ε ∙ p)                         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-identityʳ _)) ⟩
            r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝)) +ᶜ (ε ∙ p)                               ≡⟨⟩
            ε ∙ r · f p r · ⌜ ⌞ r ⌟ ⌝ + p                                           ≈˘⟨ ε ∙ +-congʳ (·-congˡ (⌜⌝-·-comm ⌞ r ⌟)) ⟩
            ε ∙ r · ⌜ ⌞ r ⌟ ⌝ · f p r + p                                           ≈˘⟨ ε ∙ +-congʳ (·-assoc _ _ _) ⟩
            ε ∙ (r · ⌜ ⌞ r ⌟ ⌝) · f p r + p                                         ≈⟨ ε ∙ +-congʳ (·-congʳ ·⌜⌞⌟⌝) ⟩
            ε ∙ r · f p r + p                                                       ≈⟨ +ᶜ-comm _ _ ⟩
            ε ∙ p + r · f p r                                                       ∎

    opaque

      -- If mode 𝟘ᵐ is allowed then the function f satisfies a certain inequality.

      f-≤-p+rf : T 𝟘ᵐ-allowed → f p r ≤ p + r · f p r
      f-≤-p+rf ok = headₘ-monotone (≤-p+rf (▸τ′ ok))

------------------------------------------------------------------------
-- Usage properties that hold for "arbitrary" usage relations with a
-- certain anstaz for the natrec rule (and some type restrictions).

module Natrec₂
  (usage-relation-natrec : Usage-relation-natrec₂)
  -- Weak unit types are allowed
  (Unit-ok : Unitʷ-allowed)
  -- Certain Σ-types are allowed
  (Σ-ok : ∀ {r} → Σʷ-allowed r 𝟘)
  where

  -- The properties that hold for the first natrec ansatz hold also
  -- for this one.

  open Natrec₁ (Natrec₂→Natrec₁ usage-relation-natrec) Unit-ok Σ-ok public
