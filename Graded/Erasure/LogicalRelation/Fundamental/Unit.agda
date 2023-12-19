------------------------------------------------------------------------
-- Graded.Erasure validity of the unit type.
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_)
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Fundamental.Unit
  {a k} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Definition.Typed R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet R}}
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet

open import Graded.Erasure.LogicalRelation R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Conversion R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Irrelevance R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Reduction R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Subsumption R is-𝟘? ⊢Δ
open import Graded.Erasure.Extraction 𝕄 is-𝟘?

import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP

open import Definition.Untyped.Properties M

open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Consequences.RedSteps R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Irrelevance R as IS
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Unit R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode 𝕄


open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Sum hiding (id; sym)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    γ δ : Conₘ n
    Γ : Con Term n
    A B t u : Term n
    σ : Subst _ _
    σ′ : T.Subst _ _
    m : Mode
    s : Strength
    l : TypeLevel
    p q : M

Unitʳ : ⊢ Γ
      → Unit-allowed s
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Unit s ∷[ m ] U / [Γ] / [U]
Unitʳ {m = m} ⊢Γ ok =
  [Γ] , [U] , λ _ _ → Uᵣ (Unitⱼ ⊢Δ ok) ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

starʳ :  ⊢ Γ
      → Unit-allowed s
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit s / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ star s ∷[ m ] Unit s / [Γ] / [Unit]
starʳ {m = m} ⊢Γ ok =
    [Γ] , [Unit]
  , λ _ _ → starᵣ (id (starⱼ ⊢Δ ok)) T.refl ◀ ⌜ m ⌝
  where
  [Γ]    = valid ⊢Γ
  [Unit] = Unitᵛ [Γ] ok


unitrecʳ′ : ([Γ] : ⊩ᵛ Γ)
           (ok : Unitʷ-allowed)
           (let [Unit] = Unitᵛ [Γ] ok)
           ([A] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Unit])
           ([A₊] : Γ ⊩ᵛ⟨ l ⟩ A [ starʷ ]₀ / [Γ])
           ([Aₜ] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Unitʷ / [Γ] / [Unit])
           ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A [ starʷ ]₀ / [Γ] / [A₊])
           (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] Unitʷ / [Γ] / [Unit])
           (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ] A [ starʷ ]₀ / [Γ] / [A₊])
          → (p PE.≡ 𝟘 → k PE.≡ 0)
         → p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ unitrec p q A t u ∷[ m ] A [ t ]₀ / [Γ] / [Aₜ]
unitrecʳ′ {n} {Γ} {l} {A} {t} {u} {γ} {𝟘ᵐ} {p} {δ} {q}
          [Γ] ok [A] [A₊] [Aₜ] [t] [u] ⊩ʳt ⊩ʳu p≡𝟘→k≡0 {σ} {σ′} [σ] σ®σ′
  with is-𝟘? 𝟘
... | yes _ = _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
unitrecʳ′ {n} {Γ} {l} {A} {t} {u} {γ} {𝟙ᵐ} {p} {δ} {q}
          [Γ] ok [A] [A₊] [Aₜ] [t] [u] ⊩ʳt ⊩ʳu p≡𝟘→k≡0 {σ} {σ′} [σ] σ®σ′ =
  let [Unit] = Unitᵛ {l = l} [Γ] ok
      [⇑σ] = liftSubstS [Γ] ⊢Δ [Unit] [σ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ])
      [σA₊] = proj₁ (unwrap [A₊] ⊢Δ [σ])
      [σAₜ] = proj₁ (unwrap [Aₜ] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      ⊢σA = escape [σA]
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift A star!) ⊢σu

      σ®σ′ᵤ = subsumptionSubst σ®σ′ λ x pγ+δ≡𝟘 →
                +-positiveʳ (PE.trans (PE.sym (lookup-distrib-+ᶜ (p ·ᶜ γ) δ x)) pγ+δ≡𝟘)
      u®u′ = ⊩ʳu [σ] σ®σ′ᵤ ◀≢𝟘 non-trivial

  in  case proj₁ ([t] ⊢Δ [σ]) of λ
    { (Unitₜ n d″ n≡n (ne (neNfₜ neK ⊢k k≡k))) →
       case is-𝟘? p of λ
         { (yes p≡𝟘) → case p≡𝟘→k≡0 p≡𝟘 of λ where
             PE.refl → ⊥-elim (noClosedNe neK)
         ; (no p≢𝟘) →
             ⊥-elim (star≢ne neK (whrDet*Term (lemma p≢𝟘 .proj₁ , starₙ) (redₜ d″ , ne neK)))
         }
    ; (Unitₜ n d n≡n starᵣ) →
      let ⊢A₊≡Aₜ = substTypeEq (refl ⊢σA) (sym (subset*Term (redₜ d)))
          ⊢A₊≡Aₜ′ = PE.subst₂ (Δ ⊢_≡_) (PE.sym (singleSubstLift A star!))
                              (PE.sym (singleSubstLift A _)) ⊢A₊≡Aₜ
          u®u″ = convTermʳ [σA₊] [σAₜ] ⊢A₊≡Aₜ′ u®u′
          redₜ = unitrec-subst* (redₜ d) ⊢σA ⊢σu′
          redₜ′ = redₜ ⇨∷* redMany (conv (unitrec-β ⊢σA ⊢σu′ ok) ⊢A₊≡Aₜ)
          redₜ″ = PE.subst (λ x → _ ⊢ unitrec p q _ _ _ ⇒* _ ∷ x)
                           (PE.sym (singleSubstLift A t)) redₜ′
      in  case is-𝟘? p of λ
          { (yes p≡𝟘) →
              let ur®ur′ = redSubstTerm* [σAₜ] u®u″ redₜ″ (T.trans T.unitrec-β T.refl)
              in  unitrec𝟘 p≡𝟘 [σAₜ] ur®ur′
          ; (no p≢𝟘) →
              let _ , d′ = lemma p≢𝟘
                  redᵥ = TP.unitrec-subst* {u = (erase u) T.[ σ′ ]} d′
                  redᵥ′ = TP.red*concat redᵥ (T.trans T.unitrec-β T.refl)
                  ur®ur′ = redSubstTerm* [σAₜ] u®u″ redₜ″ redᵥ′
              in  unitrecω p≢𝟘 [σAₜ] ur®ur′
          }
    }
  where
  lemma : (p PE.≢ 𝟘) → Δ ⊢ t [ σ ] ⇒* starʷ ∷ Unitʷ × erase t T.[ σ′ ] T.⇒* T.star
  lemma p≢𝟘 =
    let σ®σ′ₜ = subsumptionSubst σ®σ′ λ x pγ+δ≡𝟘 →
                 case zero-product (PE.trans (PE.sym (lookup-distrib-·ᶜ γ p x))
                                             (+-positiveˡ (PE.trans (PE.sym (lookup-distrib-+ᶜ (p ·ᶜ γ) δ x))
                                                          pγ+δ≡𝟘))) of λ where
                   (inj₁ p≡𝟘) → ⊥-elim (p≢𝟘 p≡𝟘)
                   (inj₂ γx≡𝟘) → γx≡𝟘
        σ®σ′ₜ′ = PE.subst (λ m → σ ® σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ])
                          (PE.sym (≢𝟘→ᵐ·≡ p≢𝟘)) σ®σ′ₜ

    in  case ⊩ʳt [σ] σ®σ′ₜ′ ◀≢𝟘 (λ x →
             non-trivial (PE.trans (PE.sym (PE.cong ⌜_⌝ (≢𝟘→ᵐ·≡ {m = 𝟙ᵐ} p≢𝟘))) x)) of λ where
        (starᵣ d d′) → d , d′
  ur = unitrec p q A t u
  unitrec𝟘 : p PE.≡ 𝟘 → ([B] : Δ ⊩⟨ l ⟩ B)
           → ur [ σ ] ®⟨ l ⟩ T.unitrec T.star (erase u) T.[ σ′ ] ∷ B / [B]
           → ur [ σ ] ®⟨ l ⟩ erase ur T.[ σ′ ] ∷ B ◂ 𝟙 / [B]
  unitrec𝟘 p≡𝟘 [B] ur®ur′ with is-𝟘? p
  ... | yes _ = ur®ur′ ◀ 𝟙
  ... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
  unitrecω : p PE.≢ 𝟘 → ([B] : Δ ⊩⟨ l ⟩ B)
           → ur [ σ ] ®⟨ l ⟩ T.unitrec (erase t) (erase u) T.[ σ′ ] ∷ B / [B]
           → ur [ σ ] ®⟨ l ⟩ erase ur T.[ σ′ ] ∷ B ◂ 𝟙 / [B]
  unitrecω p≢𝟘 [B] ur®ur′ with is-𝟘? p
  ... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
  ... | no _ = ur®ur′ ◀ 𝟙


unitrecʳ : ([Γ] : ⊩ᵛ Γ)
           (ok : Unitʷ-allowed)
           ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unitʷ / [Γ])
           ([A] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Unit])
           ([A₊] : Γ ⊩ᵛ⟨ l ⟩ A [ starʷ ]₀ / [Γ])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Unitʷ / [Γ] / [Unit])
           ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A [ starʷ ]₀ / [Γ] / [A₊])
           (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] Unitʷ / [Γ] / [Unit])
           (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ] A [ starʷ ]₀ / [Γ] / [A₊])
         → (p PE.≡ 𝟘 → k PE.≡ 0)
         → ∃ λ [Aₜ] → p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ unitrec p q A t u ∷[ m ] A [ t ]₀ / [Γ] / [Aₜ]
unitrecʳ {n} {Γ} {l} {A} {t} {u} {p} {γ} {m} {δ}
         [Γ] ok [Unit] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu p≡𝟘→k≡0 =
  let [Aₜ] = substS [Γ] [Unit] [A] [t]
      [Unit]′ = Unitᵛ [Γ] ok
      [A]′ = IS.irrelevance ([Γ] ∙ [Unit]) ([Γ] ∙ [Unit]′) [A]
      [t]′ = IS.irrelevanceTerm {t = t} [Γ] [Γ] [Unit] [Unit]′ [t]
      ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Unit] [Unit]′ ⊩ʳt
  in  [Aₜ] , unitrecʳ′ [Γ] ok [A]′ [A₊] [Aₜ] [t]′ [u] ⊩ʳt′ ⊩ʳu p≡𝟘→k≡0
