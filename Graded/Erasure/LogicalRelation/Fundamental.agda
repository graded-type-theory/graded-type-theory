------------------------------------------------------------------------
-- The fundamental lemma of the logical relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Type-restrictions TR

open Definition.Untyped M
open Definition.Typed TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Weakening 𝕄 UR
open import Graded.Mode 𝕄

open import Definition.Untyped.Names-below M
open import Definition.Untyped.Properties M
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Names-below TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Weakening TR hiding (wk)
open import Definition.Typed.Weakening.Definition TR
open import Definition.Typed.Well-formed TR

import Graded.Erasure.LogicalRelation
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Fundamental.Empty
import Graded.Erasure.LogicalRelation.Fundamental.Identity
import Graded.Erasure.LogicalRelation.Fundamental.Level
import Graded.Erasure.LogicalRelation.Fundamental.Lift
import Graded.Erasure.LogicalRelation.Fundamental.Nat
import Graded.Erasure.LogicalRelation.Fundamental.Pi-Sigma
import Graded.Erasure.LogicalRelation.Fundamental.Unit
import Graded.Erasure.LogicalRelation.Fundamental.Universe
import Graded.Erasure.LogicalRelation.Conversion
import Graded.Erasure.LogicalRelation.Hidden

open import Graded.Erasure.Target as T using (Strictness)
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
import Graded.Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N using (Nat)
open import Tools.Product as Σ
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum
import Tools.PropositionalEquality as PE

private
  variable
     α β n o : Nat
     ∇ : DCon (Term 0) _
     Γ Δ : Con Term n
     t t′ u A A′ B : Term n
     v v′ : T.Term n
     γ δ : Conₘ n
     p q : M
     x : Fin n
     m : Mode

-- One way to create an Assumptions record.

assumptions :
  ∀ {_⇛_∷_} ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
  glassify ∇ »⊢ Δ → Strictness →
  Is-reduction-relation (glassify ∇ » Δ) _⇛_∷_ →
  Assumptions
assumptions {∇} ⊢Δ s rr = record
  { ts                    = glassify ∇
  ; vs                    = eraseDCon s ∇
  ; ⊢Δ                    = ⊢Δ
  ; str                   = s
  ; is-reduction-relation = rr
  }

-- A lemma.

module _
  (⊢Δ : glassify ∇ »⊢ Δ)
  ⦃ ok : No-equality-reflection or-empty Δ ⦄
  {s : Strictness}
  {_⇛_∷_}
  ⦃ is-reduction-relation :
      Is-reduction-relation (glassify ∇ » Δ) _⇛_∷_ ⦄
  where

  open Graded.Erasure.LogicalRelation.Hidden
         (assumptions ⊢Δ s is-reduction-relation)

  opaque

    -- A fundamental lemma for variables.

    fundamentalVar :
      x ∷ A ∈ Γ →
      γ ▸[ m ] var x →
      γ ▸ Γ ⊩ʳ var x ∷[ m ∣ n ] A
    fundamentalVar {x} {A} {Γ} {γ} {m} {n} x∈Γ ▸x =
      ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} _ →
      σ ® σ′ ∷[ m ∣ n ] Γ ◂ γ                 →⟨ (λ σ®σ′ → ®∷[∣]◂⇔ .proj₁ σ®σ′ .proj₂ x∈Γ) ⟩
      σ x ® σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩  →⟨ subsumption-®∷◂ (lemma m (inv-usage-var ▸x)) ⟩
      σ x ® σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝            □
      where
      lemma :
        ∀ m →
        γ ≤ᶜ 𝟘ᶜ , x ≔ ⌜ m ⌝ →
        ⌜ m ⌝ · γ ⟨ x ⟩ PE.≡ 𝟘 →
        ⌜ m ⌝ PE.≡ 𝟘
      lemma 𝟘ᵐ = λ _ _ → PE.refl
      lemma 𝟙ᵐ = curry (
        γ ≤ᶜ 𝟘ᶜ , x ≔ 𝟙 × 𝟙 · γ ⟨ x ⟩ PE.≡ 𝟘  →⟨ Σ.map (PE.subst (_≤_ _) (update-lookup 𝟘ᶜ x) ∘→ lookup-monotone _)
                                                   (PE.trans (PE.sym (·-identityˡ _))) ⟩
        γ ⟨ x ⟩ ≤ 𝟙 × γ ⟨ x ⟩ PE.≡ 𝟘          →⟨ uncurry (flip (PE.subst (_≤ _))) ⟩
        𝟘 ≤ 𝟙                                 →⟨ 𝟘≰𝟙 ⟩
        ⊥                                     →⟨ ⊥-elim ⟩
        𝟙 PE.≡ 𝟘                              □)

-- The fundamental lemma, and a variant for terms in fully erased
-- contexts.

module Fundamental
  {∇ : DCon (Term 0) o}
  (FA : Fundamental-assumptions (glassify ∇ » Δ))
  {s : Strictness}
  {_⇛_∷_}
  ⦃ is-reduction-relation :
      Is-reduction-relation (glassify ∇ » Δ) _⇛_∷_ ⦄
  where

  open Fundamental-assumptions FA
  open Is-reduction-relation is-reduction-relation

  private

    as : Assumptions
    as = assumptions well-formed s is-reduction-relation

  open Graded.Erasure.LogicalRelation.Fundamental.Empty UR as consistent
  open Graded.Erasure.LogicalRelation.Fundamental.Identity as
  open Graded.Erasure.LogicalRelation.Fundamental.Level as
  open Graded.Erasure.LogicalRelation.Fundamental.Lift as
  open Graded.Erasure.LogicalRelation.Fundamental.Nat as
  open Graded.Erasure.LogicalRelation.Fundamental.Pi-Sigma UR as
  open Graded.Erasure.LogicalRelation.Fundamental.Unit as
  open Graded.Erasure.LogicalRelation.Fundamental.Universe as
  open Graded.Erasure.LogicalRelation.Hidden as

  -- A lemma used to prove the fundamental lemma.
  --
  -- The main parts of this proof are located in Graded.Erasure.LogicalRelation.Fundamental.X
  -- The general proof strategy of these is the following:
  -- To show that t is valid, find t′ in whnf such that t ⇒* t′ and show that t′ is valid.
  -- The result that t is valid then follows from the logical relation being closed under
  -- reduction (see Graded.Erasure.LogicalRelation.Reduction).

  private opaque

    fundamental′ :
      glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
      Names< n t → γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] A
    fundamental′ {m = 𝟘ᵐ} ⊢t _ _ =
      ▸⊩ʳ∷[𝟘ᵐ]
    fundamental′ (Levelⱼ ⊢Γ _) _ _ =
      Levelʳ (⊢zeroᵘ ⊢Γ)
    fundamental′ (zeroᵘⱼ ok _) _ _ =
      zeroᵘʳ ok
    fundamental′ (sucᵘⱼ ⊢l) _ _ =
      sucᵘʳ (inversion-Level-⊢ (wf-⊢∷ ⊢l))
    fundamental′ (supᵘⱼ ⊢l _) _ _ =
      supᵘʳ (inversion-Level-⊢ (wf-⊢∷ ⊢l))
    fundamental′ (Uⱼ ⊢t) _ _ =
      Uʳ ⊢t
    fundamental′ (Liftⱼ ⊢l₁ ⊢l₂ _) _ _ =
      Liftʳ (⊢supᵘₗ ⊢l₁ ⊢l₂)
    fundamental′ (liftⱼ ⊢t _ ⊢u) ▸lift (lift <n) =
      let ▸u = inv-usage-lift ▸lift in
      liftʳ ⊢t ⊢u (fundamental′ ⊢u ▸u <n)
    fundamental′ (lowerⱼ ⊢t) ▸lower (lower <n) =
      lowerʳ (fundamental′ ⊢t (inv-usage-lower ▸lower) <n)
    fundamental′ (ΠΣⱼ ⊢t _ _ _) _ _ =
      ΠΣʳ ⊢t
    fundamental′ (ℕⱼ _) _ _ =
      ℕʳ
    fundamental′ (Emptyⱼ _) _ _ =
      Emptyʳ
    fundamental′ (Unitⱼ _ _) _ _ =
      Unitʳ
    fundamental′ (var _ x∈Γ) ▸x _ =
      fundamentalVar well-formed x∈Γ ▸x
    fundamental′
      {Γ} {γ} {m} {n} (defn {α} {A′ = A} _ α↦ PE.refl) _ (defn <n) =
      let t , α↦t∈  = glass-↦∈ α↦
          α↦erase-t = ↦erase∈eraseDCon′ α↦t∈
      in
      ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} _ →
      σ ® σ′ ∷[ m ∣ n ] Γ ◂ γ                             →⟨ proj₁ ∘→ ®∷[∣]◂⇔ .proj₁ ⟩

      Definitions-related m n                             ⇔⟨ Definitions-related⇔ ⟩→

      (∀ {α t A v} →
       α N.< n →
       α ↦ t ∷ A ∈ glassify ∇ →
       α T.↦ v ∈ eraseDCon s ∇ →
       wk wk₀ t ® T.wk wk₀ v ∷ wk wk₀ A ◂ ⌜ m ⌝)          →⟨ (λ hyp → hyp <n α↦t∈ α↦erase-t) ⟩

      wk wk₀ t ® T.wk wk₀ (erase s t) ∷ wk wk₀ A ◂ ⌜ m ⌝  →⟨ ®∷◂-⇐* (⇒*→⇛ (redMany (δ-red well-formed α↦t∈ PE.refl PE.refl)))
                                                               (T.trans (T.δ-red α↦erase-t) T.refl) ⟩

      defn α ® T.defn α ∷ wk wk₀ A ◂ ⌜ m ⌝                ≡⟨ PE.cong (_ ® _ ∷_◂ _) $ PE.sym wk-wk₀-[]≡ ⟩→

      defn α ® T.defn α ∷ wk wk₀ A [ σ ] ◂ ⌜ m ⌝          □
    fundamental′ (lamⱼ _ ⊢t ok) ▸lam (lam <n) =
      case inv-usage-lam ▸lam of λ
        (invUsageLam ▸t γ≤δ) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤δ $
      lamʳ ok ⊢t (fundamental′ ⊢t ▸t <n)
    fundamental′ (⊢t ∘ⱼ ⊢u) ▸∘ (app <n₁ <n₂) =
      case inv-usage-app ▸∘ of λ
        (invUsageApp ▸t ▸u γ≤δ+pη) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤δ+pη $
      ∘ʳ ⊢u (fundamental′ ⊢t ▸t <n₁) (fundamental′ ⊢u ▸u <n₂)
    fundamental′ (prodⱼ {k = 𝕤} ⊢B ⊢t ⊢u ok) ▸prod (prod <n₁ <n₂) =
      case inv-usage-prodˢ ▸prod of λ
        (invUsageProdˢ ▸t ▸u γ≤pδ∧η) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤pδ∧η $
      prodˢʳ ok ⊢B ⊢t ⊢u (fundamental′ ⊢t ▸t <n₁)
        (fundamental′ ⊢u ▸u <n₂)
    fundamental′ (prodⱼ {k = 𝕨} ⊢B ⊢t ⊢u ok) ▸prod (prod <n₁ <n₂) =
      case inv-usage-prodʷ ▸prod of λ
        (invUsageProdʷ ▸t ▸u γ≤pδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤pδ+η $
      prodʷʳ ok ⊢B ⊢t ⊢u (fundamental′ ⊢t ▸t <n₁)
        (fundamental′ ⊢u ▸u <n₂)
    fundamental′ (fstⱼ _ ⊢t) ▸fst (fst <n) =
      case inv-usage-fst ▸fst of λ
        (invUsageFst _ _ ▸t γ≤δ _) →
      fstʳ ⊢t (fundamental′ ⊢t (sub ▸t γ≤δ) <n) ▸fst
    fundamental′ (sndⱼ _ ⊢t) ▸snd (snd <n) =
      case inv-usage-snd ▸snd of λ
        (invUsageSnd ▸t γ≤δ) →
      sndʳ ⊢t (fundamental′ ⊢t (sub ▸t γ≤δ) <n)
    fundamental′
      {m = 𝟙ᵐ} (prodrecⱼ ⊢C ⊢t ⊢u _) ▸prodrec (prodrec _ <n₂ <n₃) =
      case inv-usage-prodrec ▸prodrec of λ
        (invUsageProdrec ▸t ▸u _ ok γ≤rδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤rδ+η $
      prodrecʳ ⊢C ⊢t ⊢u (fundamental′ ⊢t ▸t <n₂)
        (fundamental′ ⊢u ▸u <n₃)
        (case closed-or-no-erased-matches of λ where
           (inj₁ nem) r≡𝟘 → ⊥-elim (nem non-trivial .proj₁ ok r≡𝟘)
           (inj₂ k≡0) _   → k≡0 , PE.sym (glassify-idem _))
    fundamental′ (zeroⱼ _) _ _ =
      zeroʳ
    fundamental′ (sucⱼ ⊢t) γ▸suc (suc <n) =
      case inv-usage-suc γ▸suc of λ
        (invUsageSuc δ▸t γ≤δ) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤δ $
      sucʳ ⊢t (fundamental′ ⊢t δ▸t <n)
    fundamental′ (natrecⱼ {p} {r} ⊢t ⊢u ⊢v) γ▸nr (natrec _ <n₂ <n₃ <n₄) =
      case inv-usage-natrec γ▸nr of λ {
        (invUsageNatrec {δ} {η} {θ} δ▸t η▸u θ▸v _ γ≤χ extra) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤χ $
      natrecʳ ⊢t ⊢u ⊢v (fundamental′ ⊢t δ▸t <n₂)
        (fundamental′ ⊢u η▸u <n₃) (fundamental′ ⊢v θ▸v <n₄)
        (λ x → case extra of λ where
           invUsageNatrecNr →
             nrᶜ p r δ η θ ⟨ x ⟩ PE.≡ 𝟘                        →⟨ PE.trans (PE.sym (nrᶜ-⟨⟩ δ)) ⟩
             nr p r (δ ⟨ x ⟩) (η ⟨ x ⟩) (θ ⟨ x ⟩) PE.≡ 𝟘       →⟨ (λ hyp →
                                                                     case nr-positive hyp of λ {
                                                                       (p , q , r) → p , r , q }) ⟩
             δ ⟨ x ⟩ PE.≡ 𝟘 × θ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘  □
           (invUsageNatrecNoNr {χ = χ} χ≤δ _ χ≤θ fix) →
             χ ⟨ x ⟩ PE.≡ 𝟘                                    →⟨ (λ hyp →
                                                                       ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 χ≤δ hyp
                                                                     , ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 χ≤θ hyp
                                                                     , ⟨⟩≡𝟘→⟨⟩≡𝟘-fixpoint fix hyp) ⟩
             δ ⟨ x ⟩ PE.≡ 𝟘 × θ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘  □
           (invUsageNatrecNoNrGLB {χ} {x = q′} q′-glb χ-glb) q′θ+χ≡𝟘 →
             let q′θ≡𝟘 , χ≡𝟘 = +-positive (PE.trans (PE.sym (lookup-distrib-+ᶜ (q′ ·ᶜ θ) χ x)) q′θ+χ≡𝟘)
                 δ≡𝟘 = 𝟘≮ (≤-trans (≤-reflexive (PE.sym χ≡𝟘))
                          (≤-trans (lookup-monotone x (χ-glb .proj₁ 0))
                          (≤-reflexive (lookup-cong {δ = δ} {x = x} (nrᵢᶜ-zero {r = r} {δ = η})))))
                 θ≡𝟘 : θ ⟨ x ⟩ PE.≡ 𝟘
                 θ≡𝟘 = case zero-product (PE.trans (PE.sym (lookup-distrib-·ᶜ θ q′ x)) q′θ≡𝟘) of λ where
                          (inj₁ PE.refl) → ⊥-elim (𝟘≰𝟙 (q′-glb .proj₁ 0))
                          (inj₂ θ≡𝟘) → θ≡𝟘
                 η≡𝟘 = +-positiveˡ (𝟘≮ (≤-trans (≤-reflexive (PE.sym χ≡𝟘))
                          (≤-trans (lookup-monotone x (χ-glb .proj₁ 1))
                          (≤-reflexive (PE.trans (lookup-cong {x = x} (nrᵢᶜ-suc {r = r} {γ = δ} {η} {0}))
                            (lookup-distrib-+ᶜ η (r ·ᶜ nrᵢᶜ r δ η 0) x))))))
             in  δ≡𝟘 , θ≡𝟘 , η≡𝟘)}
    fundamental′ (emptyrecⱼ _ ⊢t) ▸t (emptyrec _ <n₂) =
      case inv-usage-emptyrec ▸t of λ
        (invUsageEmptyrec ▸t _ ok γ≤pδ) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤pδ $
      emptyrecʳ ok ⊢t (fundamental′ ⊢t ▸t <n₂)
    fundamental′ (starⱼ _ ok) _ _ =
      starʳ ok
    fundamental′
      {m = 𝟙ᵐ} (unitrecⱼ ⊢A ⊢t ⊢u ok) γ▸ur (unitrec _ <n₂ <n₃) =
      case inv-usage-unitrec γ▸ur of λ
        (invUsageUnitrec _ δ▸t η▸u ok′ γ≤pδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ γ≤pδ+η $
      unitrecʳ ⊢A ⊢t ⊢u (fundamental′ ⊢t δ▸t <n₂)
        (fundamental′ ⊢u η▸u <n₃)
        (λ p≡𝟘 → case closed-or-no-erased-matches of λ where
           (inj₁ nem) → inj₂ (nem non-trivial .proj₂ .proj₁ ok′ p≡𝟘)
           (inj₂ k≡0) → inj₁ (k≡0 , PE.sym (glassify-idem _)))
    fundamental′ (Idⱼ ⊢A _ _) _ _ =
      Idʳ (inversion-U-Level (wf-⊢∷ ⊢A))
    fundamental′ (rflⱼ ⊢t) _ _ =
      rflʳ ⊢t
    fundamental′ {γ} {m = 𝟙ᵐ} (Jⱼ _ ⊢B ⊢u _ ⊢w) ▸J (J _ _ _ <n₄ _ <n₆) =
      case inv-usage-J ▸J of λ where
        (invUsageJ₀₂ em _ _ _ ▸u _ _ γ≤) →
          Jʳ ⊢B ⊢u ⊢w γ≤ (fundamental′ ⊢u ▸u <n₄)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0 , PE.sym (glassify-idem _)
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
                 of λ ())
        (invUsageJ₀₁ {γ₃} {γ₄} em _ _ _ _ _ ▸u _ _ γ≤) →
          subsumption-▸⊩ʳ∷[]
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₃ +ᶜ γ₄)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₃ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₃ ⟩
               (γ₃ ∧ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             □) $
          Jʳ ⊢B ⊢u ⊢w (∧ᶜ-decreasingʳ γ₃ _) (fundamental′ ⊢u ▸u <n₄)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0 , PE.sym (glassify-idem _)
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
                 of λ ())
        (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ _ _ ▸u _ ▸w γ≤) →
          subsumption-▸⊩ʳ∷[]
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                                        →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₅ ∘→
                                                                        ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 {γ = γ₄ +ᶜ _}
                                                                          (≤ᶜ-reflexive $
                                                                           ≈ᶜ-trans
                                                                             (≈ᶜ-trans (≈ᶜ-sym (+ᶜ-assoc _ _ _)) $
                                                                              +ᶜ-congʳ (+ᶜ-comm _ _)) $
                                                                           +ᶜ-assoc _ _ _) ∘→
                                                                        proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                        proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₂ ⟩
               (γ₄ +ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘                               →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₄ ⟩
               (γ₄ ∧ᶜ γ₆) ⟨ x ⟩ PE.≡ 𝟘                               □)
            (Jʳ ⊢B ⊢u ⊢w (∧ᶜ-decreasingˡ γ₄ _) (fundamental′ ⊢u ▸u <n₄)
               (inj₂
                  (_ , ∧ᶜ-decreasingʳ γ₄ _ , fundamental′ ⊢w ▸w <n₆)))
    fundamental′ {γ} {m = 𝟙ᵐ} (Kⱼ ⊢B ⊢u ⊢v ok) ▸K (K _ _ _ <n₄ <n₅) =
      case inv-usage-K ▸K of λ where
        (invUsageK₀₂ em _ _ _ ▸u _ γ≤) →
          Kʳ ⊢B ⊢u ⊢v ok γ≤ (fundamental′ ⊢u ▸u <n₄)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0 , PE.sym (glassify-idem _)
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
                 of λ ())
        (invUsageK₀₁ {γ₃} {γ₄} em _ _ _ _ ▸u _ γ≤) →
          subsumption-▸⊩ʳ∷[]
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₃ +ᶜ γ₄)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₃ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₃ ⟩
               (γ₃ ∧ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             □) $
          Kʳ ⊢B ⊢u ⊢v ok (∧ᶜ-decreasingʳ γ₃ _) (fundamental′ ⊢u ▸u <n₄)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0 , PE.sym (glassify-idem _)
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
                 of λ ())
        (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ _ _ ▸u ▸v γ≤) →
          subsumption-▸⊩ʳ∷[]
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                                  →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                  proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₂ ⟩
               (γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₄ ⟩
               (γ₄ ∧ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         □) $
          Kʳ ⊢B ⊢u ⊢v ok (∧ᶜ-decreasingˡ γ₄ _) (fundamental′ ⊢u ▸u <n₄)
            (inj₂ (_ , ∧ᶜ-decreasingʳ γ₄ _ , fundamental′ ⊢v ▸v <n₅))
    fundamental′ ([]-congⱼ ⊢l _ _ _ ⊢v ok) _ _ =
      []-congʳ
        (case closed-or-no-erased-matches of λ where
           (inj₁ nem) → ⊥-elim (nem non-trivial .proj₂ .proj₂ .proj₁ ok)
           (inj₂ k≡0) → k≡0 , PE.sym (glassify-idem _))
        ⊢l ⊢v ok
    fundamental′ (conv ⊢t A≡B) γ▸t <n =
      conv-▸⊩ʳ∷ A≡B (fundamental′ ⊢t γ▸t <n)

  opaque
    unfolding Definitions-related

    -- The fundamental lemma for the erasure relation.
    --
    -- Note the assumptions of the local module Fundamental.

    fundamental :
      glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
      γ ▸ Γ ⊩ʳ t ∷[ m ] A
    fundamental {Γ} {t} {A} {γ} {m} ⊢t ▸t =
                               $⟨ fundamental′ ⊢t ▸t (⊢∷→Names< ⊢t) ⟩
      γ ▸ Γ ⊩ʳ t ∷[ m ∣ o ] A  →⟨ ▸⊩ʳ∷[∣]→▸⊩ʳ∷
                                    (λ _ α↦t α↦v →
                                       subsumption-®∷◂ (⊥-elim ∘→ non-trivial) $
                                       lemma id⊇ (defn-wf (wfTerm ⊢t)) well-resourced α↦t α↦v) ⟩
      γ ▸ Γ ⊩ʳ t ∷[ m ] A      □
      where
      lemma :
        ∀ {∇′ : DCon (Term 0) n} {t A} →
        » glassify ∇ ⊇ glassify ∇′ →
        » glassify ∇′ →
        ▸[ 𝟙ᵐ ] glassify ∇′ →
        α ↦ t ∷ A ∈ glassify ∇′ →
        α T.↦ v ∈ eraseDCon s ∇′ →
        wk wk₀ t ® T.wk wk₀ v ∷ wk wk₀ A ◂ 𝟙
      lemma {∇′ = ε} _ _ _ ()
      lemma
        {v} {∇′ = ∇′∙@(∇′ ∙!)} {t} {A}
        ∇⊇∇′∙ »∇′∙t@(∙ᵗ[ ⊢t ]) ▸∇′∙ α↦t α↦v =
        let ∇⊇∇′ = »⊇-trans ∇⊇∇′∙ (stepᵗ₁ ⊢t)

            erase-t≡v : erase s t PE.≡ v
            erase-t≡v = TP.↦∈-deterministic (↦erase∈eraseDCon′ α↦t) α↦v

            ih :
              β ↦ t′ ∷ A′ ∈ glassify ∇′ →
              erase s t′ PE.≡ v′ →
              wk wk₀ t′ ® T.wk wk₀ v′ ∷ wk wk₀ A′ ◂ 𝟙
            ih β↦t′ eq =
              lemma {∇′ = ∇′} ∇⊇∇′ (defn-wf (wfTerm ⊢t)) (▸∇′∙ ∘→ there)
                β↦t′ (PE.subst (_ T.↦_∈ _) eq (↦erase∈eraseDCon′ β↦t′))
        in
        case α↦t of λ where
          (there α↦t) → ih α↦t erase-t≡v
          here        →
            PE.subst (_ ®_∷ _ ◂ _)
              (erase s (wk wk₀ t)    ≡˘⟨ wk-erase-comm _ t ⟩
               T.wk wk₀ (erase s t)  ≡⟨ PE.cong (T.wk _) erase-t≡v ⟩
               T.wk wk₀ v            ∎) $
            ▸⊩ʳ∷[∣]→®∷◂
              (λ β<α β↦t′ β↦v′ →
                 ih (<→⊇→↦→↦ β<α ∇⊇∇′ β↦t′)
                   (TP.↦∈-deterministic (↦erase∈eraseDCon′ β↦t′) β↦v′))
              (fundamental′
                 (wkTerm (wk₀∷ʷ⊇ well-formed) (defn-wkTerm ∇⊇∇′ ⊢t))
                 (PE.subst (_▸[ _ ] _) wkConₘ-ε $
                  wkUsage wk₀ (▸∇′∙ α↦t))
                 (Names<-wk (↦→Names< »∇′∙t α↦t)))
        where
        open Tools.Reasoning.PropositionalEquality

  opaque

    -- A fundamental lemma for terms in fully erased contexts.
    --
    -- Note the assumptions of the local module Fundamental.

    fundamentalErased :
      glassify ∇ » Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ m ] t →
      t ® erase s t ∷ A ◂ ⌜ m ⌝
    fundamentalErased {t} {A} {m} ⊢t ▸t =
                                 $⟨ fundamental ⊢t ▸t ⟩
      𝟘ᶜ ▸ Δ ⊩ʳ t ∷[ m ] A       →⟨ ▸⊩ʳ∷[]→®∷◂ ⟩
      t ® erase s t ∷ A ◂ ⌜ m ⌝  □

  opaque

    -- A variant of fundamentalErased.

    fundamentalErased-𝟙ᵐ :
      glassify ∇ » Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      t ® erase s t ∷ A
    fundamentalErased-𝟙ᵐ ⊢t ▸t =
      ®∷→®∷◂ω non-trivial $
      fundamentalErased ⊢t ▸t
