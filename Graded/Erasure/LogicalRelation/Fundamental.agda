------------------------------------------------------------------------
-- The fundamental lemma of the logical relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Tools.Empty
open import Tools.Sum hiding (id)
import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open Definition.Untyped M
open Definition.Typed TR
open EqRelSet {{...}}

open import Definition.LogicalRelation TR hiding (_≤_)
open import Definition.LogicalRelation.Hidden TR
import Definition.LogicalRelation.Properties TR as LP
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Properties TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR
import Definition.LogicalRelation.Substitution.Introductions.Var TR as V

import Definition.LogicalRelation.Fundamental TR as F
import Definition.LogicalRelation.Irrelevance TR as I
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Mode 𝕄

open import Definition.Untyped.Properties M
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR

import Graded.Erasure.LogicalRelation
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Fundamental.Empty
import Graded.Erasure.LogicalRelation.Fundamental.Identity
import Graded.Erasure.LogicalRelation.Fundamental.Nat
import Graded.Erasure.LogicalRelation.Fundamental.Pi-Sigma
import Graded.Erasure.LogicalRelation.Fundamental.Unit
import Graded.Erasure.LogicalRelation.Conversion
import Graded.Erasure.LogicalRelation.Hidden
import Graded.Erasure.LogicalRelation.Irrelevance
import Graded.Erasure.LogicalRelation.Subsumption

open import Graded.Erasure.Target as T using (Strictness)
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.PropositionalEquality as PE

private
  variable
     l n : Nat
     Γ Δ : Con Term n
     t u A B : Term n
     γ δ : Conₘ n
     p q : M
     x : Fin n
     m : Mode

-- A lemma.

module _ (⊢Δ : ⊢ Δ) {s : Strictness} where

  open Graded.Erasure.LogicalRelation.Hidden
         (record { ⊢Δ = ⊢Δ; str = s })

  opaque

    -- A fundamental lemma for variables.

    fundamentalVar :
      ⊢ Γ →
      x ∷ A ∈ Γ →
      γ ▸[ m ] var x →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ var x ∷[ m ] A
    fundamentalVar {x} {A} {γ} {m} ⊢Γ x∈Γ ▸x =
      ▸⊩ʳ∷⇔ .proj₂
        ( wf-⊩ᵛ∷ (emb-⊩ᵛ∷ LP.≤¹ (varᵛ x∈Γ (F.valid ⊢Γ) .proj₂))
        , λ {σ = σ} {σ′ = σ′} σ®σ′ →
            case ®∷[]◂→ σ®σ′ x∈Γ of λ
              (l , _ , _ , σx®σ′x) →
                                                         $⟨ σx®σ′x ⟩
            σ x ®⟨ l ⟩ σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩  →⟨ subsumption-®∷◂ (lemma m (inv-usage-var ▸x)) ⟩
            σ x ®⟨ l ⟩ σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝            →⟨ emb-®∷◂ LP.≤¹ ⟩
            σ x ®⟨ ¹ ⟩ σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝            □
        )
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
  (FA : Fundamental-assumptions Δ)
  {s : Strictness}
  where

  open Fundamental-assumptions FA

  private

    as : Assumptions
    as = record { ⊢Δ = well-formed; str = s }

  open Graded.Erasure.LogicalRelation as
  open Graded.Erasure.LogicalRelation.Fundamental.Empty UR as consistent
  open Graded.Erasure.LogicalRelation.Fundamental.Identity as
  open Graded.Erasure.LogicalRelation.Fundamental.Nat as
  open Graded.Erasure.LogicalRelation.Fundamental.Pi-Sigma UR as
  open Graded.Erasure.LogicalRelation.Fundamental.Unit as
  open Graded.Erasure.LogicalRelation.Conversion as
  open Graded.Erasure.LogicalRelation.Hidden as
  open Graded.Erasure.LogicalRelation.Irrelevance as
  open Graded.Erasure.LogicalRelation.Subsumption as

  -- The fundamental lemma for the erasure relation.
  --
  -- Note the assumptions of the local module Fundamental.
  --
  -- The main parts of this proof are located in Graded.Erasure.LogicalRelation.Fundamental.X
  -- The general proof strategy of these is the following:
  -- To show that t is valid, find t′ in whnf such that t ⇒* t′ and show that t′ is valid.
  -- The result that t is valid then follows from the logical relation being closed under
  -- reduction (see Graded.Erasure.LogicalRelation.Reduction).

  opaque
    unfolding _▸_⊩ʳ⟨_⟩_∷[_]_

    fundamental :
      Γ ⊢ t ∷ A → γ ▸[ m ] t →
      ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
        γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A]
    fundamental {m = 𝟘ᵐ} ⊢t _ with is-𝟘? 𝟘
    ... | yes 𝟘≡𝟘 =
      case F.fundamental (syntacticTerm ⊢t) of λ ([Γ] , [A]) →
        [Γ] , [A] , _
    ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
    fundamental (ΠΣⱼ {F = A} {G = B} ⊢A _ _) _ =
      ΠΣʳ {A = A} {B = B} (wfTerm ⊢A)
    fundamental (ℕⱼ ⊢Γ) _ =
      ℕʳ ⊢Γ
    fundamental (Emptyⱼ ⊢Γ) γ▸t = Emptyʳ ⊢Γ
    fundamental (Unitⱼ ⊢Γ _) _ =
      Unitʳ ⊢Γ
    fundamental (var ⊢Γ x∈Γ) ▸x =
      fundamentalVar well-formed ⊢Γ x∈Γ ▸x
    fundamental (lamⱼ ⊢A ⊢t ok) ▸lam =
      case inv-usage-lam ▸lam of λ
        (invUsageLam ▸t γ≤δ) →
      subsumption-▸⊩ʳ∷[]-≤ {t = lam _ _} γ≤δ $
      lamʳ ok (F.fundamental-⊩ᵛ ⊢A) (F.fundamental-⊩ᵛ∷ ⊢t)
        (fundamental ⊢t ▸t)
    fundamental (⊢t ∘ⱼ ⊢u) ▸∘ =
      case inv-usage-app ▸∘ of λ
        (invUsageApp ▸t ▸u γ≤δ+pη) →
      subsumption-▸⊩ʳ∷[]-≤ {t = _ ∘⟨ _ ⟩ _} γ≤δ+pη $
      ∘ʳ ⊢u (fundamental ⊢t ▸t) (fundamental ⊢u ▸u)
    fundamental (prodⱼ {k = 𝕤} _ ⊢B ⊢t ⊢u ok) ▸prod =
      case inv-usage-prodˢ ▸prod of λ
        (invUsageProdˢ ▸t ▸u γ≤pδ∧η) →
      subsumption-▸⊩ʳ∷[]-≤ {t = prodˢ _ _ _} γ≤pδ∧η $
      prodˢʳ ok (F.fundamental-⊩ᵛ ⊢B) (F.fundamental-⊩ᵛ∷ ⊢t) ⊢u
        (fundamental ⊢t ▸t) (fundamental ⊢u ▸u)
    fundamental (prodⱼ {k = 𝕨} _ ⊢B ⊢t ⊢u ok) ▸prod =
      case inv-usage-prodʷ ▸prod of λ
        (invUsageProdʷ ▸t ▸u γ≤pδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ {t = prodʷ _ _ _} γ≤pδ+η $
      prodʷʳ ok (F.fundamental-⊩ᵛ ⊢B) (F.fundamental-⊩ᵛ∷ ⊢t) ⊢u
        (fundamental ⊢t ▸t) (fundamental ⊢u ▸u)
    fundamental (fstⱼ _ _ ⊢t) ▸fst =
      case inv-usage-fst ▸fst of λ
        (invUsageFst _ _ ▸t γ≤δ _) →
      fstʳ (fundamental ⊢t (sub ▸t γ≤δ)) ▸fst
    fundamental (sndⱼ _ _ ⊢t) ▸snd =
      case inv-usage-snd ▸snd of λ
        (invUsageSnd ▸t γ≤δ) →
      sndʳ ⊢t (fundamental ⊢t (sub ▸t γ≤δ))
    fundamental {m = 𝟙ᵐ} (prodrecⱼ {A = C} ⊢A ⊢B ⊢C ⊢t ⊢u _) ▸prodrec =
      case inv-usage-prodrec ▸prodrec of λ
        (invUsageProdrec ▸t ▸u _ ok γ≤rδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ {t = prodrec _ _ _ C _ _} γ≤rδ+η $
      prodrecʳ (F.fundamental-⊩ᵛ ⊢C) ⊢t ⊢u (fundamental ⊢t ▸t)
        (fundamental ⊢u ▸u)
        (case closed-or-no-erased-matches of λ where
           (inj₁ nem) r≡𝟘 → ⊥-elim (nem non-trivial .proj₁ ok r≡𝟘)
           (inj₂ k≡0) _   → k≡0)
    fundamental (zeroⱼ ⊢Γ) _ =
      zeroʳ ⊢Γ
    fundamental (sucⱼ {n = t} ⊢t) γ▸suc =
      case inv-usage-suc γ▸suc of λ
        (invUsageSuc δ▸t γ≤δ) →
      subsumption-▸⊩ʳ∷[]-≤ {t = suc t} γ≤δ $
      sucʳ ⊢t (fundamental ⊢t δ▸t)
    fundamental
      (natrecⱼ {A} {z = t} {s = u} {p} {r} {n = v} ⊢A ⊢t ⊢u ⊢v)
      γ▸nr =
      case inv-usage-natrec γ▸nr of λ {
        (invUsageNatrec {δ} {η} {θ} δ▸t η▸u θ▸v _ γ≤χ extra) →
      subsumption-▸⊩ʳ∷[]-≤ {t = natrec _ _ _ A t u v} γ≤χ $
      natrecʳ (F.fundamental-⊩ᵛ ⊢A) ⊢t ⊢u ⊢v (fundamental ⊢t δ▸t)
        (fundamental ⊢u η▸u) (fundamental ⊢v θ▸v)
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
             δ ⟨ x ⟩ PE.≡ 𝟘 × θ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘  □) }
    fundamental
      {Γ = Γ} {γ = γ}
      (emptyrecⱼ {A = A} {t = t} {p = p} ⊢A ⊢t) ▸t =
        case inv-usage-emptyrec ▸t of λ
          (invUsageEmptyrec ▸t _ ok γ≤pδ) →
        subsumption-▸⊩ʳ∷[]-≤ {t = emptyrec p A t} γ≤pδ $
        emptyrecʳ ok (F.fundamental-⊩ᵛ ⊢A) (F.fundamental-⊩ᵛ∷ ⊢t)
          (fundamental ⊢t ▸t)
    fundamental (starⱼ ⊢Γ ok) _ =
      starʳ ⊢Γ ok
    fundamental {m = 𝟙ᵐ} (unitrecⱼ {A} ⊢A ⊢t ⊢u ok) γ▸ur =
      case inv-usage-unitrec γ▸ur of λ
        (invUsageUnitrec δ▸t η▸u _ ok′ γ≤pδ+η) →
      subsumption-▸⊩ʳ∷[]-≤ {t = unitrec _ _ A _ _} γ≤pδ+η $
      unitrecʳ (F.fundamental-⊩ᵛ ⊢A) (F.fundamental-⊩ᵛ∷ ⊢t)
        (F.fundamental-⊩ᵛ∷ ⊢u) (fundamental ⊢t δ▸t) (fundamental ⊢u η▸u)
        (λ p≡𝟘 → case closed-or-no-erased-matches of λ where
           (inj₁ nem) → inj₂ (nem non-trivial .proj₂ .proj₁ ok′ p≡𝟘)
           (inj₂ k≡0) → inj₁ k≡0)
    fundamental (Idⱼ {A} {t} {u} ⊢A _ _) _ =
      Idʳ {A = A} {t = t} {u = u} (wfTerm ⊢A)
    fundamental (rflⱼ ⊢t) _ =
      rflʳ ⊢t
    fundamental
      {γ} {m = 𝟙ᵐ} (Jⱼ {A} {t} {B} {u} {v} {w} _ _ ⊢B ⊢u _ ⊢w) ▸J =
      case F.fundamental-⊩ᵛ ⊢B of λ
        ⊩B →
      case inv-usage-J ▸J of λ where
        (invUsageJ₀₂ em _ _ _ ▸u _ _ γ≤) →
          Jʳ ⊩B ⊢u ⊢w γ≤ (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
                 of λ ())
        (invUsageJ₀₁ {γ₃} {γ₄} em _ _ _ _ _ ▸u _ _ γ≤) →
          subsumption-▸⊩ʳ∷[] {t = J _ _ A t B u v w}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₃ +ᶜ γ₄)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₃ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₃ ⟩
               (γ₃ ∧ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             □) $
          Jʳ ⊩B ⊢u ⊢w (∧ᶜ-decreasingʳ γ₃ _) (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
                 of λ ())
        (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ _ _ ▸u _ ▸w γ≤) →
          subsumption-▸⊩ʳ∷[] {t = J _ _ A t B u v w}
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
            (Jʳ ⊩B ⊢u ⊢w (∧ᶜ-decreasingˡ γ₄ _) (fundamental ⊢u ▸u)
               (inj₂ (_ , ∧ᶜ-decreasingʳ γ₄ _ , _ , fundamental ⊢w ▸w)))
    fundamental {γ} {m = 𝟙ᵐ} (Kⱼ {t} {A} {B} {u} {v} _ ⊢B ⊢u ⊢v ok) ▸K =
      case F.fundamental-⊩ᵛ ⊢B of λ
        ⊩B →
      case inv-usage-K ▸K of λ where
        (invUsageK₀₂ em _ _ _ ▸u _ γ≤) →
          Kʳ ⊩B ⊢u ⊢v ok γ≤ (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
                 of λ ())
        (invUsageK₀₁ {γ₃} {γ₄} em _ _ _ _ ▸u _ γ≤) →
          subsumption-▸⊩ʳ∷[] {t = K _ A t B u v}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                      →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₃ +ᶜ γ₄)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₃ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₃ +ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₃ ⟩
               (γ₃ ∧ᶜ γ₄) ⟨ x ⟩ PE.≡ 𝟘             □) $
          Kʳ ⊩B ⊢u ⊢v ok (∧ᶜ-decreasingʳ γ₃ _) (fundamental ⊢u ▸u)
            (inj₁ $ case closed-or-no-erased-matches of λ where
               (inj₂ k≡0) → k≡0
               (inj₁ nem) →
                 case
                   PE.trans (PE.sym em)
                     (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
                 of λ ())
        (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ _ _ ▸u ▸v γ≤) →
          subsumption-▸⊩ʳ∷[] {t = K _ A t B u v}
            (λ x →
               γ ⟨ x ⟩ PE.≡ 𝟘                                  →⟨ ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤ ⟩
               (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) ⟨ x ⟩ PE.≡ 𝟘      →⟨ ·ᶜ-zero-product-⟨⟩ (γ₂ +ᶜ _) ⟩
               ω PE.≡ 𝟘 ⊎ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘  →⟨ (λ { (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘); (inj₂ hyp) → hyp }) ⟩
               (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘             →⟨ proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₃ ∘→
                                                                  proj₂ ∘→ +ᶜ-positive-⟨⟩ γ₂ ⟩
               (γ₄ +ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         →⟨ +ᶜ-⟨⟩-≡-𝟘-→-∧ᶜ-⟨⟩-≡-𝟘 γ₄ ⟩
               (γ₄ ∧ᶜ γ₅) ⟨ x ⟩ PE.≡ 𝟘                         □) $
          Kʳ ⊩B ⊢u ⊢v ok (∧ᶜ-decreasingˡ γ₄ _) (fundamental ⊢u ▸u)
            (inj₂ (_ , ∧ᶜ-decreasingʳ γ₄ _ , _ , fundamental ⊢v ▸v))
    fundamental ([]-congⱼ _ _ ⊢v ok) _ =
      []-congʳ
        (case closed-or-no-erased-matches of λ where
           (inj₁ nem) → ⊥-elim (nem non-trivial .proj₂ .proj₂ .proj₁ ok)
           (inj₂ k≡0) → k≡0)
        ⊢v ok
    fundamental (conv {t} ⊢t A≡B) γ▸t =
      conv-▸⊩ʳ∷ {t = t} (F.fundamental-⊩ᵛ≡ A≡B) (fundamental ⊢t γ▸t)

  -- A fundamental lemma for terms in fully erased contexts.
  --
  -- Note the assumptions of the local module Fundamental.

  fundamentalErased :
    Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ m ] t →
    ∃ λ ([A] : Δ ⊩⟨ ¹ ⟩ A) → t ®⟨ ¹ ⟩ erase s t ∷ A ◂ ⌜ m ⌝ / [A]
  fundamentalErased {t = t} {A = A} {m = m} ⊢t 𝟘▸t =
    [A]′ , lemma m ⊩ʳt
    where
    [Δ]-[A]-⊩ʳt = fundamental ⊢t 𝟘▸t
    [Δ] = [Δ]-[A]-⊩ʳt .proj₁
    [A] = [Δ]-[A]-⊩ʳt .proj₂ .proj₁
    ⊩ʳt = [Δ]-[A]-⊩ʳt .proj₂ .proj₂
    [id]′ = idSubstS [Δ]
    ⊢Δ′ = soundContext [Δ]
    [id] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ well-formed [id]′
    [idA] = proj₁ (unwrap [A] {σ = idSubst} well-formed [id])
    [A]′ = I.irrelevance′ (subst-id A) [idA]

    lemma :
      ∀ m →
      𝟘ᶜ ▸ Δ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Δ] / [A] →
      t ®⟨ ¹ ⟩ erase s t ∷ A ◂ ⌜ m ⌝ / [A]′
    lemma 𝟘ᵐ with is-𝟘? 𝟘
    ... | yes 𝟘≡𝟘 = _
    ... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)

    lemma 𝟙ᵐ ⊩ʳt with is-𝟘? 𝟙
    ... | yes 𝟙≡𝟘 = ⊥-elim (non-trivial 𝟙≡𝟘)
    ... | no 𝟙≢𝟘 =
      PE.subst₂ (λ x y → x ®⟨ ¹ ⟩ y ∷ A / [A]′)
        (subst-id t) (TP.subst-id (erase s t)) t®t″
      where
      id®id′ = erasedSubst {σ′ = T.idSubst} [Δ] [id]
      t®t′ = ⊩ʳt [id] id®id′
      t®t″ = irrelevanceTerm′ (subst-id A) [idA] [A]′ t®t′

  opaque
    unfolding _▸_⊩ʳ⟨_⟩_∷[_]_

    -- A variant of fundamental.

    fundamental-⊩ʳ∷ :
      Γ ⊢ t ∷ A → γ ▸[ m ] t →
      γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A
    fundamental-⊩ʳ∷ = fundamental

  opaque
    unfolding _®⟨_⟩_∷_◂_

    -- A variant of fundamentalErased.

    fundamentalErased-®∷◂ :
      Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ m ] t →
      t ®⟨ ¹ ⟩ erase s t ∷ A ◂ ⌜ m ⌝
    fundamentalErased-®∷◂ = fundamentalErased

  opaque

    -- Another variant of fundamentalErased.

    fundamentalErased-𝟙ᵐ :
      Δ ⊢ t ∷ A → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      t ®⟨ ¹ ⟩ erase s t ∷ A
    fundamentalErased-𝟙ᵐ ⊢t ▸t =
      ®∷→®∷◂ω non-trivial $
      fundamentalErased-®∷◂ ⊢t ▸t
