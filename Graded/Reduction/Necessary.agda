------------------------------------------------------------------------
-- An investigation into necessary properties for subject reduction
-- to hold.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Reduction.Necessary
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Type-restrictions TR
open Usage-restrictions UR
open Modality 𝕄
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Restrictions.Natrec 𝕄
import Graded.Reduction TR UR as R
import Graded.Usage UR as U
import Graded.Usage.Inversion UR as UI
import Graded.Usage.Properties UR as UP
import Graded.Usage.Weakening UR as UW

open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Syntactic TR
import Definition.Typed.Reasoning.Type TR as TEq
open import Definition.Typed.Substitution TR
open import Definition.Typed.Weakening TR as W hiding (wk)
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+; 2+; 3+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  n i : Nat
  l : Universe-level
  Γ : Cons _ _
  Δ : Con Term _
  γ δ η θ : Conₘ _
  t u v z s k A B : Term _
  m m′ : Mode
  p q r : M
  ρ : Wk _ _
  x : Fin _

------------------------------------------------------------------------
-- "Arbitrary" usage relations satisfying some properties and ansatz for
-- certain usage rules.

-- A usage relation with some requirements

record Usage-relation : Set (lsuc (a ⊔ b)) where
  no-eta-equality
  infix 10 _▸[_]_ ▸[_]_
  field
    _▸[_]_ : Conₘ n → Mode → Term n → Set (a ⊔ b)

  -- Well-resourced definitions

  ▸[_]_ : Mode → DCon (Term 0) n → Set (a ⊔ b)
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
    Σʷₘ : γ ▸[ m ] A → δ ∙ ⌜ m ⌝ · q ▸[ m ] B → γ +ᶜ δ ▸[ m ] Σʷ p , q ▷ A ▹ B
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
    ▸-· : γ ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ·ᵐ m ] t
    ▸ᵐ : γ ▸[ m ] t → γ ≤ᶜ ⌜ m ⌝ ·ᶜ γ

    -- Subject reduction
    usagePresTerm :
      ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u

-- A usage relation with a usage rule for natrec on a certain form.

record Usage-relation-natrec₁ : Set (lsuc (a ⊔ b)) where
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
      η ▸[ m ] k → θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
      f p r ·ᶜ η +ᶜ g p r γ δ ▸[ m ] natrec p q r A z s k
    inv-usage-natrec :
      γ ▸[ m ] natrec p q r A z s k →
      ∃₄ λ δ₁ δ₂ δ₃ δ₄ →
      δ₁ ▸[ m ] z × δ₂ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
      δ₃ ▸[ m ] k × δ₄ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A ×
      γ ≤ᶜ f p r ·ᶜ δ₃ +ᶜ g p r δ₁ δ₂

-- A usage relation with a usage rule for natrec on a certain form.
-- This ansatz is similar to the one above but the function g does
-- not depend on the grade p.

record Usage-relation-natrec₂ : Set (lsuc (a ⊔ b)) where
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
      η ▸[ m ] k → θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
      f p r ·ᶜ η +ᶜ g r γ δ ▸[ m ] natrec p q r A z s k
    inv-usage-natrec :
      γ ▸[ m ] natrec p q r A z s k →
      ∃₄ λ δ₁ δ₂ δ₃ δ₄ →
      δ₁ ▸[ m ] z × δ₂ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s ×
      δ₃ ▸[ m ] k × δ₄ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A ×
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

-- A usage relation with a usage rule for unitrec on a certain form.

record Usage-relation-unitrec : Set (lsuc (a ⊔ b)) where
  no-eta-equality
  field
    usage-relation : Usage-relation

  open Usage-relation usage-relation public
  field
    -- Anstaz for the usage rule for unitrec
    f : M → M
    g : M → Conₘ n → Conₘ n
    unitrecₘ :
      γ ▸[ m ᵐ· p ] t → δ ▸[ m ] u →
      η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
      Unitrec-allowed m p q →
      f p ·ᶜ γ +ᶜ g p δ ▸[ m ] unitrec l p q A t u

-- A usage relation with a usage rule for prodrec on a certain form.

record Usage-relation-prodrec : Set (lsuc (a ⊔ b)) where
  no-eta-equality
  field usage-relation : Usage-relation

  open Usage-relation usage-relation public
  field
    f : (p r : M) (γ δ : Conₘ n) → Conₘ n
    prodrecₘ :
      γ ▸[ m ᵐ· r ] t →
      δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
      η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
      Prodrec-allowed m r p q →
      f p r γ δ ▸[ m ] prodrec r p q A t u

------------------------------------------------------------------------
-- Given certain assumptions, the usage relation satisfies the
-- properties and ansatzes above.

module _
  -- The proof of subject reduction for the usage relation uses this
  -- assumption:
  (Unitʷ-η→ :
     ∀ {m p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed m p q → ⌜ m ⌝ PE.≢ 𝟘 →
     p ≤ 𝟘)
  where

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
      ; ▸-· = UP.▸-·
      ; ▸ᵐ = UP.▸ᵐ
      ; usagePresTerm = R.usagePresTerm Unitʷ-η→
      }

  opaque
    unfolding ▸[]-Usage-relation

    ▸[]-factoring-nr-Usage-relation-natrec₁ :
      ⦃ has-nr : Nr-available ⦄
      ⦃ nr-factoring : Is-factoring-nr _ (Natrec-mode-Has-nr has-nr) ⦄ →
      Usage-relation-natrec₁
    ▸[]-factoring-nr-Usage-relation-natrec₁ ⦃ has-nr ⦄ ⦃ nr-factoring ⦄ = record
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

  opaque
    unfolding ▸[]-Usage-relation

    ▸[]-usage-relation-unitrec : Usage-relation-unitrec
    ▸[]-usage-relation-unitrec = record
      { usage-relation = ▸[]-Usage-relation
      ; f = idᶠ
      ; g = λ _ → idᶠ
      ; unitrecₘ = U.unitrecₘ
      }

  opaque
    unfolding ▸[]-Usage-relation

    ▸[]-usage-relation-prodrec : Usage-relation-prodrec
    ▸[]-usage-relation-prodrec = record
      { usage-relation = ▸[]-Usage-relation
      ; f = λ p r γ δ → r ·ᶜ γ +ᶜ δ
      ; prodrecₘ = U.prodrecₘ
      }

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

    -- A usage rule for sink.

    ▸sink : (γ : Conₘ n) → ⌜ m ⌝ ·ᶜ γ ▸[ m ] sink γ
    ▸sink ε =
      PE.subst (_▸[_]_ _ _) (PE.sym sink-ε-≡) starʷₘ
    ▸sink {m} (γ ∙ p) =
      let open ≤ᶜ-reasoning
          ▸t = sub (prodʷₘ varₘ (wkUsage (▸sink γ))) $ begin
            ⌜ m ⌝ ·ᶜ γ            ∙ ⌜ m ⌝ · p               ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩
            ⌜ m ⌝ ·ᶜ γ            ∙ p · ⌜ m ⌝               ≈˘⟨ +ᶜ-identityˡ _ ∙ ·⌜ᵐ·⌝ m ⟩
            𝟘ᶜ +ᶜ ⌜ m ⌝ ·ᶜ γ      ∙ p · ⌜ m ᵐ· p ⌝          ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ∙ +-identityʳ _ ⟩
            p ·ᶜ 𝟘ᶜ +ᶜ ⌜ m ⌝ ·ᶜ γ ∙ p · ⌜ m ᵐ· p ⌝ + 𝟘      ≡⟨⟩
            p ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· p ⌝) +ᶜ (⌜ m ⌝ ·ᶜ γ ∙ 𝟘) ∎
      in  PE.subst (λ x → ⌜ m ⌝ ·ᶜ (γ ∙ p) ▸[ _ ] x) (PE.sym sink-∙-≡) ▸t

  opaque

    -- A usage rule for sink: sink γ is well-resourced under context γ at mode 𝟙ᵐ.

    ▸¹sink : γ ▸[ 𝟙ᵐ ] sink γ
    ▸¹sink =
      sub (▸sink _)
        (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (·ᶜ-congʳ ⌜𝟙ᵐ⌝) (·ᶜ-identityˡ _))))

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
      ≤ᶜ-trans (inv-usage-sink ▸γ) (≤ᶜ-reflexive (≈ᶜ-trans (·ᶜ-congʳ ⌜𝟙ᵐ⌝) (·ᶜ-identityˡ _)))

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

      ▸S : 𝟘ᶜ ∙ ⌜ 𝟙ᵐ ⌝ · 𝟘 ∙ ⌜ 𝟙ᵐ ⌝ · 𝟙 ▸[ 𝟙ᵐ ] S p r δ
      ▸S {p} {r} {δ} =
        let ▸δ = sub (wkUsage ▸Sink-Δᴺ) $ begin
              𝟘ᶜ ∙ ⌜ 𝟙ᵐ ⌝ · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ ∙ 𝟘 ∎
            open ≤ᶜ-reasoning
            ▸Σ = sub (Σʷₘ ℕₘ ▸δ) $ begin
              𝟘ᶜ ∙ ⌜ 𝟙ᵐ ⌝ · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
              𝟘ᶜ +ᶜ 𝟘ᶜ        ∎
        in  sub (Σʷₘ varₘ ▸Σ) $ begin
          𝟘ᶜ ∙ ⌜ 𝟙ᵐ ⌝ · 𝟘 ∙ ⌜ 𝟙ᵐ ⌝ · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ⟩
          𝟘ᶜ ∙ 𝟘     ∙ ⌜ 𝟙ᵐ ⌝           ≈˘⟨ +ᶜ-identityʳ _ ⟩
          (𝟘ᶜ , x0 ≔ ⌜ 𝟙ᵐ ⌝) +ᶜ 𝟘ᶜ      ∎
        where
        open ≤ᶜ-reasoning

    opaque

      -- A term used in the proofs below.

      α : (p r : M) (γ δ : Conₘ n) → Term (1+ n)
      α p r γ δ = natrec 𝟘 𝟘 𝟙 (U 0) (wk1 (Z γ)) (S p r δ) (var x0)

    opaque
      unfolding α

      α₀≡ :
        α p r γ δ [ zero ]₀ PE.≡
        natrec 𝟘 𝟘 𝟙 (U 0) (Sink Δᴺ γ)
          (Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 4 ]′ (Sink Δᴺ δ))) zero
      α₀≡ {p} {r} {γ} {δ} =
        PE.cong₂ (λ x y → natrec 𝟘 𝟘 𝟙 (U 0) x y zero)
          Z₀≡ S₀≡

    opaque
      unfolding α

      α₊≡ :
        α p r γ δ [ suc (var x1) ]↑² PE.≡
        natrec 𝟘 𝟘 𝟙 (U 0) (wk₂ (Sink Δᴺ γ))
          (Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ))) (suc (var x1))
      α₊≡ {r} =
        PE.cong₂ (λ x y → natrec 𝟘 𝟘 𝟙 (U 0) x y (suc (var x1))) Z₊≡ S₊≡

    opaque
      unfolding α Z S

      wk1α≡ :
        wk1 (α p r γ δ) PE.≡
        natrec 𝟘 𝟘 𝟙 (U 0) (wk₂ (Sink Δᴺ γ))
          (Σʷ r , 𝟘 ▷ var x0 ▹ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 6 ]′ (Sink Δᴺ δ)))
          (var x1)
      wk1α≡ {r} =
        PE.cong₂ (λ z s → natrec 𝟘 𝟘 𝟙 (U 0) z s (var x1))
          (wk-comp _ _ _)
          (PE.cong (λ x → Σʷ r , 𝟘 ▷ _ ▹ (Σʷ _ , 𝟘 ▷ _ ▹ x)) (wk-comp _ _ _))

    opaque
      unfolding α

      ⊢α : Γᴺ ⊢ α p r γ δ
      ⊢α = univ (natrecⱼ (wkTerm (stepʷ id (ℕⱼ ⊢Γᴺ)) ⊢Z) ⊢S (var ⊢Γᴺ here))

    opaque
      unfolding α

      ▸¹α : tailₘ (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ) ∙ f 𝟘 𝟙 + headₘ {n = n} (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ) ▸[ 𝟙ᵐ ] α {n = n} p r γ δ
      ▸¹α {p} {r} =
        let ▸U = sub Uₘ (≤ᶜ-refl {γ = 𝟘ᶜ} ∙ ≤-reflexive (·-zeroʳ _))
            η = g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ
            open ≤ᶜ-reasoning
        in  sub (natrecₘ (wkUsage ▸Z) ▸S varₘ ▸U) $ begin
          tailₘ η ∙ f 𝟘 𝟙 + headₘ η                ≈˘⟨ +ᶜ-identityˡ _ ∙ PE.refl ⟩
          (𝟘ᶜ ∙ f 𝟘 𝟙) +ᶜ (tailₘ η ∙ headₘ η)      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) ⟩
          f 𝟘 𝟙 ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ (tailₘ η ∙ headₘ η) ≡⟨ PE.cong₂ (λ x y → f 𝟘 𝟙 ·ᶜ (𝟘ᶜ ∙ x) +ᶜ y) (PE.sym ⌜𝟙ᵐ⌝) (headₘ-tailₘ-correct η) ⟩
          f 𝟘 𝟙 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ 𝟙ᵐ ⌝) +ᶜ η         ∎

    opaque

      ▸α : ⌜ m ⌝ ·ᶜ (tailₘ (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ) ∙ f 𝟘 𝟙 + headₘ {n = n} (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ)) ▸[ m ] α {n = n} p r γ δ
      ▸α {m} = PE.subst (λ x → ⌜ m ⌝ ·ᶜ (tailₘ (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ) ∙ f 𝟘 𝟙 + headₘ (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ)) ▸[ x ] _) (·ᵐ-identityʳ _) (▸-· ▸¹α)

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
      ▸ζ = ▸¹sink

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
        sub (prodʷₘ varₘ (prodʷₘ varₘ (wkUsage ▸¹sink))) $ begin
        δ                        ∙ ⌜ 𝟙ᵐ ⌝ · p                     ∙ ⌜ 𝟙ᵐ ⌝ · r                     ≈⟨ ≈ᶜ-refl ∙ ·-congʳ ⌜𝟙ᵐ⌝ ∙ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
        δ                        ∙ 𝟙 · p                     ∙ 𝟙 · r                     ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ∙ ·-identityˡ _ ⟩
        δ                        ∙ p                         ∙ r                         ≈˘⟨ ≈ᶜ-refl ∙ ·⌜⌞⌟⌝ ∙ ·⌜⌞⌟⌝  ⟩
        δ                        ∙ p · ⌜ ⌞ p ⌟ ⌝             ∙ r · ⌜ ⌞ r ⌟ ⌝             ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ⟩
        𝟘ᶜ +ᶜ δ                  ∙ 𝟘 + p · ⌜ ⌞ p ⌟ ⌝         ∙ r · ⌜ ⌞ r ⌟ ⌝ + 𝟘         ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (+ᶜ-identityˡ _) ∙
                                                                                             +-cong (·-zeroʳ _) (+-identityʳ _) ∙
                                                                                             +-congˡ (+-identityʳ _) ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ δ       ∙ r · 𝟘 + p · ⌜ ⌞ p ⌟ ⌝ + 𝟘 ∙ r · ⌜ ⌞ r ⌟ ⌝ + 𝟘 + 𝟘     ≈˘⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _)) ∙ PE.refl ∙
                                                                                             +-congˡ (+-congʳ (·-zeroʳ _)) ⟩
        r ·ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ δ  ∙ r · 𝟘 + p · ⌜ ⌞ p ⌟ ⌝ + 𝟘 ∙ r · ⌜ ⌞ r ⌟ ⌝ + p · 𝟘 + 𝟘 ≡⟨⟩
        r ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ r ⌟ ⌝) +ᶜ p ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ ⌞ p ⌟ ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)          ≈˘⟨ ≈ᶜ-refl ∙ +-congˡ (+-congʳ (·-congˡ (⌜⌝-cong ᵐ·-identityˡ))) ∙
                                                                                              +-congʳ (·-congˡ (⌜⌝-cong ᵐ·-identityˡ)) ⟩
        r ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ 𝟙ᵐ ᵐ· r ⌝) +ᶜ p ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ 𝟙ᵐ ᵐ· p ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)      ∎
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
        natrec p (f 𝟘 𝟙 + headₘ {n = n} (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ)) r
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
        η ▸[ m ] σ p r δ [ t , u ]₁₀ →
        ∃₂ λ η₁ η₂ → η₁ ▸[ m ᵐ· p ] t × η₂ ▸[ m ᵐ· r ] u × η ≤ᶜ ⌜ m ⌝ ·ᶜ (r ·ᶜ η₂ +ᶜ p ·ᶜ η₁ +ᶜ δ)
      inv-usage-σ[,] {η} {m} {p} {r} {δ} ▸σ =
        let η₁ , η₂ , ▸u , ▸v , η≤ = inv-usage-prodʷ ▸σ
            η₃ , η₄ , ▸t , ▸δ , η₂≤ = inv-usage-prodʷ ▸v
            ▸δ′ = PE.subst (λ x → η₄ ▸[ _ ] x) (wk₂-[,] {t = sink δ}) ▸δ
            open ≤ᶜ-reasoning
        in  _ , _ , ▸t , ▸u , (begin
          η                                                              ≤⟨ η≤ ⟩
          r ·ᶜ η₁ +ᶜ η₂                                                  ≤⟨ +ᶜ-monotoneʳ η₂≤ ⟩
          r ·ᶜ η₁ +ᶜ p ·ᶜ η₃ +ᶜ η₄                                       ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸ᵐ ▸u)) (+ᶜ-monotone (·ᶜ-monotoneʳ (▸ᵐ ▸t)) (inv-usage-sink ▸δ′)) ⟩
          r ·ᶜ ⌜ m ᵐ· r ⌝ ·ᶜ η₁ +ᶜ p ·ᶜ ⌜ m ᵐ· p ⌝ ·ᶜ η₃ +ᶜ ⌜ m ⌝ ·ᶜ δ   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-congʳ (·ᶜ-assoc _ _ _)) ⟩
          (r · ⌜ m ᵐ· r ⌝) ·ᶜ η₁ +ᶜ (p · ⌜ m ᵐ· p ⌝) ·ᶜ η₃ +ᶜ ⌜ m ⌝ ·ᶜ δ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·⌜ᵐ·⌝ _)) (+ᶜ-congʳ (·ᶜ-congʳ (·⌜ᵐ·⌝ _))) ⟩
          (r · ⌜ m ⌝) ·ᶜ η₁ +ᶜ (p · ⌜ m ⌝) ·ᶜ η₃ +ᶜ ⌜ m ⌝ ·ᶜ δ           ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (⌜⌝-·-comm _)) (+ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm _))) ⟩
          (⌜ m ⌝ · r) ·ᶜ η₁ +ᶜ (⌜ m ⌝ · p) ·ᶜ η₃ +ᶜ ⌜ m ⌝ ·ᶜ δ           ≈⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-congʳ (·ᶜ-assoc _ _ _)) ⟩
          ⌜ m ⌝ ·ᶜ r ·ᶜ η₁ +ᶜ ⌜ m ⌝ ·ᶜ p ·ᶜ η₃ +ᶜ ⌜ m ⌝ ·ᶜ δ             ≈˘⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          ⌜ m ⌝ ·ᶜ r ·ᶜ η₁ +ᶜ ⌜ m ⌝ ·ᶜ (p ·ᶜ η₃ +ᶜ δ)                    ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m ⌝ ·ᶜ (r ·ᶜ η₁ +ᶜ p ·ᶜ η₃ +ᶜ δ)                             ∎)

    opaque
      unfolding σ

      inv-usage-σ[k,τ] :
        η ▸[ m ] σ p r δ [ sucᵏ i , τ p r γ δ i ]₁₀ →
        ∃ λ θ → θ ▸[ m ᵐ· r ] τ p r γ δ i × η ≤ᶜ ⌜ m ⌝ ·ᶜ (δ +ᶜ r ·ᶜ θ)
      inv-usage-σ[k,τ] {η} {p} {r} {δ} ▸σ =
        let η₁ , η₂ , ▸i , ▸τ , η≤ = inv-usage-σ[,] ▸σ
            open ≤ᶜ-reasoning
        in  _ , ▸τ , ≤ᶜ-trans η≤ (·ᶜ-monotoneʳ (begin
          r ·ᶜ η₂ +ᶜ p ·ᶜ η₁ +ᶜ δ ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-sucᵏ ▸i))) ⟩
          r ·ᶜ η₂ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ δ ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _)) ⟩
          r ·ᶜ η₂ +ᶜ 𝟘ᶜ +ᶜ δ      ≈⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
          r ·ᶜ η₂ +ᶜ δ            ≈⟨ +ᶜ-comm _ _ ⟩
          δ +ᶜ r ·ᶜ η₂            ∎))

    opaque
      unfolding τ

      -- The context nrᵢᶜ r γ δ i is an upper bound on valid contexts
      -- for the term τ p r γ δ i.

      ≤-nrᵢᶜ : ∀ i → η ▸[ m ] τ p r γ δ i → η ≤ᶜ ⌜ m ⌝ ·ᶜ nrᵢᶜ r γ δ i
      ≤-nrᵢᶜ {η} {m} {r} {γ} {δ} 0 ▸nr =
        let open ≤ᶜ-reasoning in begin
          η                     ≤⟨ inv-usage-ζ (usagePresTerm (λ ()) ▸nr (natrec-zero ⊢ζ ⊢σ)) ⟩
          ⌜ m ⌝ ·ᶜ γ            ≈˘⟨ ·ᶜ-congˡ nrᵢᶜ-zero ⟩
          ⌜ m ⌝ ·ᶜ nrᵢᶜ r γ δ 0 ∎
      ≤-nrᵢᶜ {η} {m} {p} {r} {γ} {δ} (1+ i) ▸nr =
        let ▸s = usagePresTerm (λ ()) ▸nr (natrec-suc ⊢ζ ⊢σ (⊢sucᵏ ⊢Γᴺ))
            θ , ▸IH , η≤ = inv-usage-σ[k,τ] ▸s
            open ≤ᶜ-reasoning
        in  begin
          η                                                 ≤⟨ η≤ ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ r ·ᶜ θ)                            ≤⟨ ·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ (≤-nrᵢᶜ i ▸IH))) ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ r ·ᶜ ⌜ m ᵐ· r ⌝ ·ᶜ nrᵢᶜ r γ δ i)   ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-assoc _ _ _)) ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ (r · ⌜ m ᵐ· r ⌝) ·ᶜ nrᵢᶜ r γ δ i)  ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congʳ (·⌜ᵐ·⌝ _))) ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ (r · ⌜ m ⌝) ·ᶜ nrᵢᶜ r γ δ i)       ≈˘⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congʳ (⌜⌝-·-comm _))) ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ (⌜ m ⌝ · r) ·ᶜ nrᵢᶜ r γ δ i)       ≈⟨ ·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-assoc _ _ _)) ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ ⌜ m ⌝ ·ᶜ r ·ᶜ nrᵢᶜ r γ δ i)        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m ⌝ ·ᶜ δ +ᶜ ⌜ m ⌝ ·ᶜ ⌜ m ⌝ ·ᶜ r ·ᶜ nrᵢᶜ r γ δ i ≈⟨ +ᶜ-congˡ ·ᶜ-idem-⌜⌝ ⟩
          ⌜ m ⌝ ·ᶜ δ +ᶜ ⌜ m ⌝ ·ᶜ r ·ᶜ nrᵢᶜ r γ δ i          ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m ⌝ ·ᶜ (δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ i)                 ≈˘⟨ ·ᶜ-congˡ nrᵢᶜ-suc ⟩
          ⌜ m ⌝ ·ᶜ nrᵢᶜ r γ δ (1+ i) ∎

    opaque

      -- The context nrᵢᶜ r γ δ i is an upper bound on valid contexts
      -- for the term τ p r γ δ i.

      ≤-nrᵢᶜ-𝟙ᵐ : ∀ i → η ▸[ 𝟙ᵐ ] τ p r γ δ i → η ≤ᶜ nrᵢᶜ r γ δ i
      ≤-nrᵢᶜ-𝟙ᵐ {η} {r} {γ} {δ} i ▸τ = begin
        η                      ≤⟨ ≤-nrᵢᶜ i ▸τ ⟩
        ⌜ 𝟙ᵐ ⌝ ·ᶜ nrᵢᶜ r γ δ i ≈⟨ ·ᶜ-congʳ ⌜𝟙ᵐ⌝ ⟩
        𝟙 ·ᶜ nrᵢᶜ r γ δ i      ≈⟨ ·ᶜ-identityˡ _ ⟩
        nrᵢᶜ r γ δ i           ∎
        where
        open ≤ᶜ-reasoning

  opaque

    -- The context g p r γ δ is bounded from above by nrᵢᶜ r γ δ i for all i.
    -- That is, g p r γ δ is smaller than γ, δ +ᶜ r ·ᶜ γ, ….

    g-≤-nrᵢᶜ : ∀ i → g p r γ δ ≤ᶜ nrᵢᶜ r γ δ i
    g-≤-nrᵢᶜ i = ≤-nrᵢᶜ-𝟙ᵐ i ▸τ

  opaque

    -- If mode 𝟘ᵐ is allowed then g p r 𝟘ᶜ 𝟘ᶜ is equal to 𝟘ᶜ.

    g𝟘𝟘≈𝟘 : ¬ Trivialᵐ → g p r 𝟘ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
    g𝟘𝟘≈𝟘 {p} {r} {n} 𝟙ᵐ≢𝟘ᵐ =
      let 𝟘▸τ = PE.subst (λ m → 𝟘ᶜ {n} ▸[ m ] τ p r 𝟘ᶜ 𝟘ᶜ 0) (·ᵐ-zeroˡ _) $ sub (▸-· ▸τ) $ begin
                  𝟘ᶜ                    ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
                  𝟘 ·ᶜ g p r 𝟘ᶜ 𝟘ᶜ      ≈˘⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
                  ⌜ 𝟘ᵐ ⌝ ·ᶜ g p r 𝟘ᶜ 𝟘ᶜ ∎
          γ , δ , γ≤ , δ≤ , 𝟘≤g = inv-usage-τ 𝟘▸τ
          γ≤𝟘 = begin
            γ            ≤⟨ γ≤ ⟩
            ⌜ 𝟘ᵐ ⌝ ·ᶜ 𝟘ᶜ ≈⟨ ·ᶜ-zeroʳ _ ⟩
            𝟘ᶜ           ∎
          𝟘≤γ = begin
            𝟘ᶜ           ≤⟨ 𝟘≤g ⟩
            g p r γ δ    ≤⟨ g-≤-nrᵢᶜ 0 ⟩
            nrᵢᶜ r γ δ 0 ≈⟨ nrᵢᶜ-zero ⟩
            γ ∎
          γ≈𝟘 = ≤ᶜ-antisym γ≤𝟘 𝟘≤γ
          δ≤𝟘 = begin
            δ            ≤⟨ δ≤ ⟩
            ⌜ 𝟘ᵐ ⌝ ·ᶜ 𝟘ᶜ ≈⟨ ·ᶜ-zeroʳ _ ⟩
            𝟘ᶜ           ∎
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
      τ′ p r t = natrec p (f 𝟘 𝟙 + headₘ {n = 1} (g 𝟘 𝟙 𝟘ᶜ 𝟘ᶜ)) r (α p r 𝟘ᶜ 𝟘ᶜ) (ζ 𝟘ᶜ) (σ p r 𝟘ᶜ) t

    opaque
      unfolding τ′

      ▸τ′ : ¬ Trivialᵐ → ε ∙ f p r ▸[ 𝟙ᵐ ] τ′ p r (suc (var x0))
      ▸τ′ {p} {r} 𝟙ᵐ≢𝟘ᵐ = sub (natrecₘ ▸ζ ▸σ (sucₘ varₘ) ▸α) $ begin
        ε ∙ f p r                            ≈˘⟨ ε ∙ ·-identityʳ _ ⟩
        ε ∙ f p r · 𝟙                        ≈˘⟨ ε ∙ ·-congˡ ⌜𝟙ᵐ⌝ ⟩
        ε ∙ f p r · ⌜ 𝟙ᵐ ⌝                   ≈˘⟨ +ᶜ-identityʳ _ ⟩
        (ε ∙ f p r · ⌜ 𝟙ᵐ ⌝) +ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congˡ (g𝟘𝟘≈𝟘 𝟙ᵐ≢𝟘ᵐ) ⟩
        f p r ·ᶜ (ε ∙ ⌜ 𝟙ᵐ ⌝) +ᶜ g p r 𝟘ᶜ 𝟘ᶜ ∎
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
          γ                                                                           ≤⟨ γ≤ ⟩
          ⌜ 𝟙ᵐ ⌝ ·ᶜ (r ·ᶜ γ₂ +ᶜ p ·ᶜ γ₁ +ᶜ 𝟘ᶜ)                                        ≈⟨ ·ᶜ-congʳ ⌜𝟙ᵐ⌝ ⟩
          𝟙 ·ᶜ (r ·ᶜ γ₂ +ᶜ p ·ᶜ γ₁ +ᶜ 𝟘ᶜ)                                             ≈⟨ ·ᶜ-identityˡ _ ⟩
          r ·ᶜ γ₂ +ᶜ p ·ᶜ γ₁ +ᶜ 𝟘ᶜ                                                    ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
          r ·ᶜ γ₂ +ᶜ p ·ᶜ γ₁                                                          ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ γ₂≤) (·ᶜ-monotoneʳ (inv-usage-var ▸x0)) ⟩
          r ·ᶜ (f p r ·ᶜ δ₃ +ᶜ g p r δ₁ δ₂) +ᶜ p ·ᶜ (ε ∙ ⌜ 𝟙ᵐ ᵐ· p ⌝)                 ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (ε ∙ ⌜⌝-cong ᵐ·-identityˡ)) ⟩
          r ·ᶜ (f p r ·ᶜ δ₃ +ᶜ g p r δ₁ δ₂) +ᶜ p ·ᶜ (ε ∙ ⌜ ⌞ p ⌟ ⌝)                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-var ▸x0′)) (g-≤-nrᵢᶜ 0))) ⟩
          r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ 𝟙ᵐ ᵐ· r ⌝) +ᶜ nrᵢᶜ r δ₁ δ₂ 0) +ᶜ p ·ᶜ (ε ∙ ⌜ ⌞ p ⌟ ⌝) ≈⟨ +ᶜ-cong (·ᶜ-congˡ (+ᶜ-cong (ε ∙ ·-congˡ (⌜⌝-cong ᵐ·-identityˡ)) nrᵢᶜ-zero)) (ε ∙ ·⌜⌞⌟⌝) ⟩
          r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ δ₁) +ᶜ (ε ∙ p)                            ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (inv-usage-ζ ▸ζ))) ⟩
          r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ ⌜ 𝟙ᵐ ᵐ· r ⌝ ·ᶜ 𝟘ᶜ) +ᶜ (ε ∙ p)             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _))) ⟩
          r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ 𝟘ᶜ) +ᶜ (ε ∙ p)                            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-identityʳ _)) ⟩
          r ·ᶜ (f p r ·ᶜ (ε ∙ ⌜ ⌞ r ⌟ ⌝)) +ᶜ (ε ∙ p)                                  ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (ε ∙ ⌜⌝-·-comm _)) ⟩
          ε ∙ r ·  ⌜ ⌞ r ⌟ ⌝ · f p r + p                                              ≈˘⟨ ε ∙ +-congʳ (·-assoc _ _ _) ⟩
          ε ∙ (r ·  ⌜ ⌞ r ⌟ ⌝) · f p r + p                                            ≈⟨ ε ∙ +-congʳ (·-congʳ ·⌜⌞⌟⌝) ⟩
          ε ∙ r · f p r + p                                                           ≈⟨ +ᶜ-comm _ _ ⟩
          ε ∙ p + r · f p r                                                           ∎

  opaque

    -- If the mode structure is non-trivial then the function f
    -- satisfies a certain inequality.

    f-≤-p+rf : ¬ Trivialᵐ → f p r ≤ p + r · f p r
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

------------------------------------------------------------------------
-- Usage properties that hold for "arbitrary" usage relations with a
-- certain anstaz for the unitrec rule (and some type restrictions).

module Unitrec
  (usage-relation-unitrec : Usage-relation-unitrec)
  -- Weak unit types are allowed
  (Unit-ok : Unitʷ-allowed)
  -- Certain Σ-types are allowed
  (Σ-ok : ∀ {r} → Σʷ-allowed r 𝟘)
  where

  open Usage-relation-unitrec usage-relation-unitrec
  open Usage usage-relation

  private

    opaque
      unfolding Sink-allowed

      -- The Sink type is allowed.

      Sink-ok : Sink-allowed γ
      Sink-ok {γ = ε} = Unit-ok
      Sink-ok {γ = γ ∙ p} = Sink-ok {γ = γ} , Σ-ok

    opaque

      τ : M → Conₘ n → Term n
      τ p δ = unitrec 0 p 𝟘 (wk1 (Sink Δᴺ δ)) (starʷ 0) (sink δ)

    opaque
      unfolding τ

      ▸τ : Unitrec-allowed 𝟙ᵐ p 𝟘 → g p γ ▸[ 𝟙ᵐ ] τ p γ
      ▸τ {p} {γ} ok =
        let ▸A = sub (wkUsage ▸Sink-Δᴺ) (≤ᶜ-refl {γ = 𝟘ᶜ} ∙ ≤-reflexive (·-zeroʳ _))
        in  sub (unitrecₘ starʷₘ ▸¹sink ▸A ok) $ begin
          g p γ              ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ g p γ        ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          f p ·ᶜ 𝟘ᶜ +ᶜ g p γ ∎
        where
        open ≤ᶜ-reasoning


    opaque
      unfolding τ

      ▸τ→≤ : γ ▸[ m ] τ p δ → γ ≤ᶜ ⌜ m ⌝ ·ᶜ δ
      ▸τ→≤ ▸ur =
        let ⊢A = W.wk (stepʷ id (Unitⱼ ⊢Γᴺ Unit-ok)) (⊢-Sink ⊢Γᴺ Sink-ok)
            ⊢u = ⊢∷-conv-PE (⊢∷-sink ⊢Γᴺ Sink-ok) (PE.sym (wk1-sgSubst _ _))
        in  case Unitʷ-η? of λ where
          (yes η) →
            inv-usage-sink (usagePresTerm (λ ()) ▸ur (unitrec-β-η ⊢A (starⱼ ⊢Γᴺ Unit-ok) ⊢u Unit-ok η))
          (no no-η) →
            inv-usage-sink (usagePresTerm (λ ()) ▸ur (unitrec-β ⊢A ⊢u Unit-ok no-η))

  opaque

    -- The context g p γ is bounded from above by γ.

    g-≤ : Unitrec-allowed 𝟙ᵐ p 𝟘 → g p γ ≤ᶜ γ
    g-≤ {p} {γ} ok = begin
      g p γ       ≤⟨ ▸τ→≤ (▸τ ok) ⟩
      ⌜ 𝟙ᵐ ⌝ ·ᶜ γ ≈⟨ ·ᶜ-congʳ ⌜𝟙ᵐ⌝ ⟩
      𝟙 ·ᶜ γ      ≈⟨ ·ᶜ-identityˡ _ ⟩
      γ           ∎
      where
      open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Usage properties that hold for "arbitrary" usage relations with a
-- certain anstaz for the prodrec rule (and some type restrictions).

module Prodrec
  (usage-relation-prodrec : Usage-relation-prodrec)
  -- Weak unit types are allowed
  (Unit-ok : Unitʷ-allowed)
  -- Certain Σ-types are allowed
  (Σ-ok : ∀ {r} → Σʷ-allowed r 𝟘)
  where

  open Usage-relation-prodrec usage-relation-prodrec
  open Usage usage-relation

  private

    opaque
      unfolding Sink-allowed

      -- The Sink type is allowed.

      Sink-ok : Sink-allowed γ
      Sink-ok {γ = ε} = Unit-ok
      Sink-ok {γ = γ ∙ p} = Sink-ok {γ = γ} , Σ-ok

    -- Some terms and lemmas used below.

    opaque

      π : M → Conₘ n → Term n
      π p γ = prodʷ p zero (sink γ)

    opaque
      unfolding π

      ⊢π : ⊢ Γ → Γ ⊢ π p γ ∷ Σʷ p , 𝟘 ▷ ℕ ▹ wk1 (Sink (Γ .vars) γ)
      ⊢π ⊢Γ =
        let ⊢Sink = W.wk (stepʷ id (ℕⱼ ⊢Γ)) (⊢-Sink ⊢Γ Sink-ok)
            ⊢sink = ⊢∷-conv-PE (⊢∷-sink ⊢Γ Sink-ok) (PE.sym (wk1-sgSubst _ _))
        in  prodⱼ ⊢Sink (zeroⱼ ⊢Γ) ⊢sink Σ-ok

    opaque
      unfolding π

      ▸π : ⌜ m ⌝ ·ᶜ γ ▸[ m ] π p γ
      ▸π {m} {γ} {p} = sub (prodʷₘ zeroₘ (▸sink γ)) $ begin
        ⌜ m ⌝ ·ᶜ γ            ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ ⌜ m ⌝ ·ᶜ γ      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
        p ·ᶜ 𝟘ᶜ +ᶜ ⌜ m ⌝ ·ᶜ γ ∎
        where
        open ≤ᶜ-reasoning

    opaque

      α : (p r : M) → (γ δ : Conₘ n) → Term (1+ n)
      α p r γ δ = Σʷ r , 𝟘 ▷ (Σʷ p , 𝟘 ▷ ℕ ▹ wk₂ (Sink Δᴺ γ)) ▹ wk₂ (Sink Δᴺ δ)

    opaque
      unfolding α

      α[]↑²≡ :
        α p r γ δ [ prodʷ p (var x1) (var x0) ]↑² PE.≡
        Σʷ r , 𝟘 ▷ (Σʷ p , 𝟘 ▷ ℕ ▹ wk[ 3 ]′ (Sink Δᴺ γ)) ▹ wk[ 3 ]′ (Sink Δᴺ δ)
      α[]↑²≡ {p} {r} {δ} =
        PE.cong₂ (λ x y → Σʷ r , 𝟘 ▷ Σʷ p , 𝟘 ▷ ℕ ▹ x ▹ y)
          lemma lemma
        where
        open Tools.Reasoning.PropositionalEquality
        lemma : wk₂ A [ consSubst (wkSubst 2 idSubst) t ⇑ ] PE.≡ wk[ 3 ]′ A
        lemma {A} {t} = begin
          wk₂ A [ consSubst (wkSubst 2 idSubst) t ⇑ ]
            ≡˘⟨ PE.cong (_[ consSubst (wkSubst 2 idSubst) t ⇑ ]) (wk[]≡wk[]′ {k = 2} {t = A}) ⟩
          wk1 (wk1 A) [ consSubst (wkSubst 2 idSubst) t ⇑ ]
            ≡⟨ wk[]-⇑[] {t = wk1 A} 1 ⟩
          wk1 (wk1 A [ consSubst (wkSubst 2 idSubst) t ])
            ≡⟨ PE.cong wk1 (wk1-tail A) ⟩
          wk1 (A [ wkSubst 2 idSubst ])
            ≡˘⟨ PE.cong wk1 (wk≡subst _ _) ⟩
          wk1 (wk₂ A)
            ≡⟨ wk-comp _ _ _ ⟩
          wk[ 3 ]′ A ∎

    opaque
      unfolding α

      ⊢α : Γᴺ ⊢ A → Γᴺ »∙ A ⊢ α p r γ δ
      ⊢α ⊢A =
        let ⊢Σ = ΠΣⱼ (W.wk (stepʷ (step id) (ℕⱼ (∙ ⊢A))) (⊢-Sink ⊢Γᴺ Sink-ok)) Σ-ok
            ⊢Sink = W.wk (stepʷ (step id) ⊢Σ) (⊢-Sink ⊢Γᴺ Sink-ok)
        in  ΠΣⱼ ⊢Sink Σ-ok

    opaque
      unfolding α

      ▸α : 𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ▸[ 𝟘ᵐ ] α p r γ δ
      ▸α {r} =
        let ▸Sink₁ = sub (wkUsage ▸Sink-Δᴺ) $ begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ ∙ 𝟘          ∎
            ▸Sink₂ = sub (wkUsage ▸Sink-Δᴺ) $ begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ ∙ 𝟘           ∎
        in  sub (Σʷₘ (Σʷₘ ℕₘ ▸Sink₁) ▸Sink₂) $ begin
          𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          𝟘ᶜ               ≈˘⟨ +ᶜ-identityʳ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ         ≈˘⟨ +ᶜ-identityʳ _ ⟩
          (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ 𝟘ᶜ ∎
        where
        open ≤ᶜ-reasoning

    opaque

      υ : (p r : M) → Conₘ n → Term (2+ n)
      υ p r δ = prodʷ r (prodʷ p (var x1) (var x0)) (wk₂ (sink δ))

    opaque
      unfolding υ

      υ≡ : υ p r δ PE.≡ prodʷ r (prodʷ p (var x1) (var x0)) (wk₂ (sink δ))
      υ≡ = PE.refl

    opaque

      υ[,]≡ : υ p r δ [ t , u ]₁₀ PE.≡ prodʷ r (prodʷ p t u) (sink δ)
      υ[,]≡ {p} {r} {δ} {t} {u} = begin
        υ p r δ [ t , u ]₁₀
          ≡⟨ PE.cong (_[ t , u ]₁₀) υ≡ ⟩
        prodʷ r (prodʷ p t u) (wk₂ (sink δ) [ t , u ]₁₀)
          ≡⟨ PE.cong (λ x → prodʷ r _ x) wk₂-[,] ⟩
        prodʷ r (prodʷ p t u) (sink δ) ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque

      ⊢υ :
        Γᴺ »∙ wk1 (Sink Δᴺ γ) ⊢ υ p r δ ∷ α p r γ δ [ prodʷ p (var x1) (var x0) ]↑²
      ⊢υ {γ} {p} {r} {δ} =
        let ⊢Sinkγ = W.wk (stepʷ id (ℕⱼ ⊢Γᴺ)) (⊢-Sink ⊢Γᴺ Sink-ok)
            ⊢Sinkγ′ = W.wk (stepʷ (step (step id)) (ℕⱼ (∙ ⊢Sinkγ))) (⊢-Sink ⊢Γᴺ Sink-ok)
            ⊢Σ = ΠΣⱼ ⊢Sinkγ′ Σ-ok
            ⊢Sinkδ = W.wk (stepʷ (step (step id)) ⊢Σ) (⊢-Sink ⊢Γᴺ Sink-ok)
            ⊢x0 = ⊢∷-conv-PE (var₀ ⊢Sinkγ) (PE.trans wk[]≡wk[]′ (PE.sym (step-sgSubst (Sink Δᴺ γ) (var x1))))
            ⊢t₁ = ⊢∷-conv-PE (prodⱼ ⊢Sinkγ′ (var₁ ⊢Sinkγ) ⊢x0 Σ-ok)
                    (PE.cong (Σʷ p , 𝟘 ▷ ℕ ▹_) PE.refl)
            ⊢t₂ = ⊢∷-conv-PE (wkTerm (stepʷ (step id) ⊢Sinkγ) (⊢∷-sink ⊢Γᴺ Sink-ok))
                   (PE.sym (step-sgSubst (Sink Δᴺ δ) (prodʷ p (var x1) (var x0))))
        in  ⊢∷-conv-PE (⊢∷-cong (prodⱼ ⊢Sinkδ ⊢t₁ ⊢t₂ Σ-ok) (PE.sym υ≡)) (PE.sym α[]↑²≡)

    opaque
      unfolding υ

      ▸υ : δ ∙ ⌜ 𝟙ᵐ ⌝ · r · p ∙ ⌜ 𝟙ᵐ ⌝ · r ▸[ 𝟙ᵐ ] υ p r δ
      ▸υ {δ} {r} {p} =
        sub (prodʷₘ (prodʷₘ varₘ varₘ) (wkUsage ▸¹sink)) $ begin
          δ ∙ ⌜ 𝟙ᵐ ⌝ · r · p ∙ ⌜ 𝟙ᵐ ⌝ · r
            ≈⟨ ≈ᶜ-refl ∙ ·-congʳ ⌜𝟙ᵐ⌝ ∙ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
          δ ∙ 𝟙 · r · p ∙ 𝟙 · r
            ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ∙ ·-identityˡ _ ⟩
          δ ∙ r · p ∙ r
            ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _ ⟩
          (𝟘ᶜ ∙ r · p ∙ r) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congʳ (≈ᶜ-refl ∙ ·-congʳ ·⌜⌞⌟⌝ ∙ ·⌜⌞⌟⌝) ⟩
          (𝟘ᶜ ∙ (r · ⌜ ⌞ r ⌟ ⌝) · p ∙ r · ⌜ ⌞ r ⌟ ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ PE.sym (·-assoc _ _ _) ∙ PE.refl) ⟩
          r ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ r ⌟ ⌝ · p ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (≈ᶜ-refl ∙ ⌜⌝-·-comm ⌞ r ⌟ ∙ PE.refl)) ⟩
          r ·ᶜ (𝟘ᶜ ∙ p · ⌜ ⌞ r ⌟ ⌝ ∙ ⌜ ⌞ r ⌟ ⌝) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityˡ _)) ⟩
          r ·ᶜ ((𝟘ᶜ ∙ p · ⌜ ⌞ r ⌟ ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ r ⌟ ⌝)) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ ⌞ r ⌟ ∙ ·-zeroʳ _))) ⟩
          r ·ᶜ (p ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ r ⌟ ᵐ· p ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ r ⌟ ⌝)) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)
            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-cong (≈ᶜ-refl ∙ ·-congˡ (⌜⌝-cong (ᵐ·-congʳ ᵐ·-identityˡ)) ∙ PE.refl) (≈ᶜ-refl ∙ ⌜⌝-cong ᵐ·-identityˡ))) ⟩
          r ·ᶜ (p ·ᶜ (𝟘ᶜ ∙ ⌜ (𝟙ᵐ ᵐ· r)  ᵐ· p ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟙ᵐ ᵐ· r ⌝)) +ᶜ (δ ∙ 𝟘 ∙ 𝟘) ∎
        where
        open ≤ᶜ-reasoning

    opaque
      unfolding υ

      inv-usage-υ[,] :
        γ ▸[ m ] υ p r δ [ t , u ]₁₀ →
        ∃₂ λ γ₁ γ₂ → γ₁ ▸[ (m ᵐ· r) ᵐ· p ] t × γ₂ ▸[ m ᵐ· r ] u ×
         γ ≤ᶜ r ·ᶜ (p ·ᶜ γ₁ +ᶜ γ₂) +ᶜ ⌜ m ⌝ ·ᶜ δ
      inv-usage-υ[,] {γ} {m} {p} {r} {δ} ▸υ[,] =
        let ▸υ = PE.subst (λ x → γ ▸[ m ] x) υ[,]≡ ▸υ[,]
            γ₁ , γ₂ , ▸υ′ , ▸δ , γ≤ = inv-usage-prodʷ ▸υ
            γ₃ , γ₄ , ▸t , ▸u , γ₁≤ = inv-usage-prodʷ ▸υ′
            open ≤ᶜ-reasoning
        in  _ , _ , ▸t , ▸u , (begin
          γ                                  ≤⟨ γ≤ ⟩
          r ·ᶜ γ₁ +ᶜ γ₂                      ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ γ₁≤)
                                               (inv-usage-sink ▸δ) ⟩
          r ·ᶜ (p ·ᶜ γ₃ +ᶜ γ₄) +ᶜ ⌜ m ⌝ ·ᶜ δ ∎)

    opaque

      τ : (p r : M) (γ δ : Conₘ n) → Term n
      τ p r γ δ =
        prodrec r p 𝟘
          (α p r γ δ) (π p γ) (υ p r δ)

    opaque
      unfolding τ

      ▸τ : Prodrec-allowed 𝟙ᵐ r p 𝟘 → f p r (⌜ ⌞ r ⌟ ⌝ ·ᶜ γ) δ ▸[ 𝟙ᵐ ] τ p r γ δ
      ▸τ {r} {p} {γ} =
        prodrecₘ (PE.subst (λ m → ⌜ ⌞ r ⌟ ⌝ ·ᶜ γ ▸[ m ] π p γ) (PE.sym ᵐ·-identityˡ) ▸π) ▸υ ▸α

    opaque
      unfolding τ π

      -- The context ⌜ m ⌝ ·ᶜ (r ·ᶜ γ +ᶜ δ) is an upper bound on valid contexts
      -- for term τ p r γ δ.

      ▸τ→≤ : η ▸[ m ] τ p r γ δ → η ≤ᶜ ⌜ m ⌝ ·ᶜ (r ·ᶜ γ +ᶜ δ)
      ▸τ→≤ {η} {m} {p} {r} {γ} {δ} ▸pr =
        let ⊢sink = ⊢∷-conv-PE (⊢∷-sink ⊢Γᴺ Sink-ok) (PE.sym (wk1-sgSubst _ zero))
            ⊢Σ = ΠΣⱼ (W.wk (stepʷ id (ℕⱼ ⊢Γᴺ)) (⊢-Sink ⊢Γᴺ Sink-ok)) Σ-ok
            ▸υ[,] = usagePresTerm (λ ()) ▸pr
                      (prodrec-β-⇒ (⊢α ⊢Σ) (zeroⱼ ⊢Γᴺ) ⊢sink ⊢υ)
            η₁ , η₂ , ▸0 , ▸γ , η≤ = inv-usage-υ[,] ▸υ[,]
            open ≤ᶜ-reasoning
        in  begin
          η                                              ≤⟨ η≤ ⟩
          r ·ᶜ (p ·ᶜ η₁ +ᶜ η₂) +ᶜ ⌜ m ⌝ ·ᶜ δ              ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotone
                                                             (·ᶜ-monotoneʳ (inv-usage-zero ▸0))
                                                             (inv-usage-sink ▸γ))) ⟩
          r ·ᶜ (p ·ᶜ 𝟘ᶜ +ᶜ ⌜ m ᵐ· r ⌝ ·ᶜ γ) +ᶜ ⌜ m ⌝ ·ᶜ δ ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ _))) ⟩
          r ·ᶜ (𝟘ᶜ +ᶜ ⌜ m ᵐ· r ⌝ ·ᶜ γ) +ᶜ ⌜ m ⌝ ·ᶜ δ      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-identityˡ _)) ⟩
          r ·ᶜ (⌜ m ᵐ· r ⌝ ·ᶜ γ) +ᶜ ⌜ m ⌝ ·ᶜ δ            ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
          (r · ⌜ m ᵐ· r ⌝) ·ᶜ γ +ᶜ ⌜ m ⌝ ·ᶜ δ             ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (·⌜ᵐ·⌝ m)) ⟩
          (r · ⌜ m ⌝) ·ᶜ γ +ᶜ ⌜ m ⌝ ·ᶜ δ                  ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌜⌝-·-comm m)) ⟩
          (⌜ m ⌝ · r) ·ᶜ γ +ᶜ ⌜ m ⌝ ·ᶜ δ                  ≈⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
          ⌜ m ⌝ ·ᶜ r ·ᶜ γ +ᶜ ⌜ m ⌝ ·ᶜ δ                   ≈˘⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ⌜ m ⌝ ·ᶜ (r ·ᶜ γ +ᶜ δ)                          ∎

  opaque

    -- An inequality satisfied by the function f.

    f-≤ : Prodrec-allowed 𝟙ᵐ r p 𝟘 → f p r (⌜ ⌞ r ⌟ ⌝ ·ᶜ γ) δ ≤ᶜ r ·ᶜ γ +ᶜ δ
    f-≤ {r} {p} {γ} {δ} ok = begin
      f p r (⌜ ⌞ r ⌟ ⌝ ·ᶜ γ) δ ≤⟨ ▸τ→≤ (▸τ ok) ⟩
      ⌜ 𝟙ᵐ ⌝ ·ᶜ (r ·ᶜ γ +ᶜ δ)  ≈⟨ ·ᶜ-congʳ ⌜𝟙ᵐ⌝ ⟩
      𝟙 ·ᶜ (r ·ᶜ γ +ᶜ δ)       ≈⟨ ·ᶜ-identityˡ _ ⟩
      r ·ᶜ γ +ᶜ δ              ∎
      where
      open ≤ᶜ-reasoning

  opaque

    -- When ⌜ ⌞ r ⌟ ⌝ is equal to 𝟙 the context given by the
    -- ansatz is bounded by the one used in the "actual" usage rule for prodrec.

    ⌞r⌟≡𝟙ᵐ→f-≤ : ⌜ ⌞ r ⌟ ⌝ PE.≡ 𝟙 → Prodrec-allowed 𝟙ᵐ r p 𝟘 → f p r γ δ ≤ᶜ r ·ᶜ γ +ᶜ δ
    ⌞r⌟≡𝟙ᵐ→f-≤ {r} {p} {γ} {δ} r≡𝟙 ok = begin
      f p r γ δ                ≡˘⟨ PE.cong (λ x → f p r x δ) (≈ᶜ→≡ (·ᶜ-identityˡ _)) ⟩
      f p r (𝟙 ·ᶜ γ) δ         ≡˘⟨ PE.cong (λ x → f p r (x ·ᶜ γ) δ) r≡𝟙 ⟩
      f p r (⌜ ⌞ r ⌟ ⌝ ·ᶜ γ) δ ≤⟨ f-≤ ok ⟩
      r ·ᶜ γ +ᶜ δ              ∎
      where
      open ≤ᶜ-reasoning

  opaque

    -- When r is equal to 𝟘, the context given by the ansatz is bounded by
    -- the one used in the "actual" usage rule for prodrec when the context
    -- for the pair is 𝟘ᶜ.

    r≡𝟘→f-≤ : r PE.≡ 𝟘 → Prodrec-allowed 𝟙ᵐ r p 𝟘 → f p r 𝟘ᶜ δ ≤ᶜ r ·ᶜ 𝟘ᶜ +ᶜ δ
    r≡𝟘→f-≤ {r} {p} {δ} r≡𝟘 ok = begin
      f p r 𝟘ᶜ δ                ≡˘⟨ PE.cong (λ x → f p r x δ) (≈ᶜ→≡ (·ᶜ-zeroʳ _)) ⟩
      f p r (⌜ ⌞ r ⌟ ⌝ ·ᶜ 𝟘ᶜ) δ ≤⟨ f-≤ ok ⟩
      r ·ᶜ 𝟘ᶜ +ᶜ δ              ∎
      where
      open ≤ᶜ-reasoning
