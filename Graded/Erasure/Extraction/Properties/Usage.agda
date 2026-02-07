------------------------------------------------------------------------
-- Properties of the extraction function related to usage.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions

module Graded.Erasure.Extraction.Properties.Usage
  {a} {M : Set a}
  {𝕄 : Modality M}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (R : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
open import Graded.Erasure.Target as T
  hiding (refl; trans)
open import Graded.Erasure.Target.Properties

open import Definition.Untyped M as U
  hiding (Term; wk; _[_]; _[_,_]₁₀; liftSubst)
import Definition.Untyped.Properties M as UP

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Properties R
open import Graded.Usage.Properties.Has-well-behaved-zero R
open import Graded.Usage.Restrictions.Instance R

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List
open import Tools.Nat as Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (subst)
open import Tools.Relation
open import Tools.Sum

import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    b : Bool
    α m n : Nat
    𝕋 𝕌 : Set _
    A A₁ A₂ t t₁ t₂ t₃ t₄ u : U.Term n
    v v₁ v₂ : T.Term n
    ts : DCon (U.Term _) _
    ∇ : List (T.Term n)
    σ : U.Subst m n
    σ′ : T.Subst m n
    ρ : Wk _ _
    γ : Conₘ n
    x : Fin n
    p q r : M
    k : Strength
    s : Strictness

private

  -- A definition used in the proof of erase-[].

  OK : U.Subst n n → Conₘ n → Set a
  OK σ γ = ∀ {x} → σ x ≢ var x → x ◂ 𝟘 ∈ γ

private opaque

  -- Some lemmas used in the proof of erase-[].

  ¬◂𝟘∈,≔𝟙 :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    ¬ x ◂ 𝟘 ∈ (γ , x ≔ 𝟙)
  ¬◂𝟘∈,≔𝟙 {x} {γ} =
    x ◂ 𝟘 ∈ (γ , x ≔ 𝟙)    ⇔⟨ ◂∈⇔ ⟩→
    (γ , x ≔ 𝟙) ⟨ x ⟩ ≡ 𝟘  ≡⟨ cong (_≡ _) $ update-lookup γ x ⟩→
    𝟙 ≡ 𝟘                  →⟨ non-trivial ⟩
    ⊥                      □

  erase-[]-var :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
    (y : Fin n) →
    OK σ (𝟘ᶜ , y ≔ 𝟙) →
    erase′ b s (σ y) ≡ var y
  erase-[]-var {σ} {b} {s} y ok
    with σ y | ok {x = y} | UP.is-var? (σ y)
  … | _ | ok | UP.not-var ≢var =
    ⊥-elim $ ¬◂𝟘∈,≔𝟙 $ ok ≢var
  … | _ | ok | UP.var x with x ≟ⱽ y
  …  | yes x≡y = cong var x≡y
  …  | no x≢y  =
    ⊥-elim $ ¬◂𝟘∈,≔𝟙 $ ok (x≢y ∘→ UP.var-PE-injectivity)

  OK-⇑-∙ : OK σ γ → OK (σ U.⇑) (γ ∙ p)
  OK-⇑-∙ _      {x = x0}   ≢var = ⊥-elim $ ≢var refl
  OK-⇑-∙ erased {x = _ +1} ≢var =
    there (erased (≢var ∘→ cong U.wk1))

opaque

  -- Substituting anything for erasable variables (using a
  -- substitution of type U.Subst n n) does not affect the result of
  -- erasure (assuming that the modality has a well-behaved zero).

  erase-[] :
    {σ : U.Subst n n}
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    (∀ {x} → σ x ≢ var x → x ◂ 𝟘 ∈ γ) →
    γ ▸[ 𝟙ᵐ ] t →
    erase′ b s (t U.[ σ ]) ≡ erase′ b s t
  erase-[] ok (sub ▸t γ≤δ) =
    erase-[] (flip x◂𝟘∈γ≤δ γ≤δ ∘→ ok) ▸t
  erase-[] ok var =
    erase-[]-var _ ok
  erase-[] _ defn =
    refl
  erase-[] _ Levelₘ =
    refl
  erase-[] _ zeroᵘₘ =
    refl
  erase-[] _ (sucᵘₘ _) =
    refl
  erase-[] _ (supᵘₘ _ _) =
    refl
  erase-[] _ (Uₘ _) =
    refl
  erase-[] _ (Liftₘ _ _) =
    refl
  erase-[] ok (liftₘ ▸t) =
      erase-[] ok ▸t
  erase-[] ok (lowerₘ ▸t) =
    erase-[] ok ▸t
  erase-[] _ Emptyₘ =
    refl
  erase-[] _ (emptyrecₘ _ _ _) =
    refl
  erase-[] _ Unitₘ =
    refl
  erase-[] _ (starˢₘ _) =
    refl
  erase-[] _ starʷₘ =
    refl
  erase-[] ok (unitrecₘ {p} ▸t₁ ▸t₂ _ _) with is-𝟘? p
  … | no p≢𝟘 =
    cong₂ unitrec
      (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ+δˡ refl ∘→ ok)
         (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
      (erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
  … | yes _ =
    erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂
  erase-[] _ (ΠΣₘ _ _) =
    refl
  erase-[] ok (lamₘ {p} ▸t) with is-𝟘? p
  … | no _ =
    cong lam (erase-[] (OK-⇑-∙ ok) ▸t)
  erase-[] {b = false} ok (lamₘ ▸t) | yes _ =
    cong lam (erase-[] (OK-⇑-∙ ok) ▸t)
  erase-[] {b = true} ok (lamₘ ▸t) | yes _ =
    cong T._[ _ ]₀ (erase-[] (OK-⇑-∙ ok) ▸t)
  erase-[] ok (_∘ₘ_ {p} ▸t ▸u) with is-𝟘? p
  … | no p≢𝟘 =
    cong₂ _∘⟨ _ ⟩_ (erase-[] (x◂𝟘∈γ+δˡ refl ∘→ ok) ▸t)
      (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ+δʳ refl ∘→ ok)
         (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸u))
  erase-[] {b = false} ok (▸t ∘ₘ _) | yes _ =
    cong (_∘⟨ _ ⟩ _) (erase-[] (x◂𝟘∈γ+δˡ refl ∘→ ok) ▸t)
  erase-[] {b = true} ok (▸t ∘ₘ _) | yes _ =
    erase-[] (x◂𝟘∈γ+δˡ refl ∘→ ok) ▸t
  erase-[] ok (prodˢₘ {p} ▸t₁ ▸t₂) with is-𝟘? p
  … | yes _ =
    erase-[] (x◂𝟘∈γ∧δʳ refl ∘→ ok) ▸t₂
  … | no p≢𝟘 =
    cong₂ prod⟨ _ ⟩
      (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ∧δˡ refl ∘→ ok)
         (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
      (erase-[] (x◂𝟘∈γ∧δʳ refl ∘→ ok) ▸t₂)
  erase-[] ok (fstₘ {p} ▸t _) with is-𝟘? p
  … | yes _ =
    refl
  … | no _ =
    cong fst (erase-[] ok ▸t)
  erase-[] ok (sndₘ {p} ▸t) with is-𝟘? p
  … | yes _ =
    erase-[] ok ▸t
  … | no _ =
    cong snd (erase-[] ok ▸t)
  erase-[] ok (prodʷₘ {p} ▸t₁ ▸t₂) with is-𝟘? p
  … | yes _ =
    erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂
  … | no p≢𝟘 =
    cong₂ prod⟨ _ ⟩
      (erase-[] (x◂𝟘∈pγ refl p≢𝟘 ∘→ x◂𝟘∈γ+δˡ refl ∘→ ok)
         (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t₁))
      (erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
  erase-[] ok (prodrecₘ {r} ▸t₁ ▸t₂ _ _) with is-𝟘? r
  … | yes _ =
    cong _[ _ , _ ]₁₀
      (erase-[] (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
  … | no r≢𝟘 =
    cong₂ (erase-prodrecω _ _)
      (erase-[] (x◂𝟘∈pγ refl r≢𝟘 ∘→ x◂𝟘∈γ+δˡ refl ∘→ ok)
         (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t₁))
      (erase-[] (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δʳ refl ∘→ ok) ▸t₂)
  erase-[] _ ℕₘ =
    refl
  erase-[] _ zeroₘ =
    refl
  erase-[] ok (sucₘ ▸t) =
    cong suc⟨ _ ⟩ (erase-[] ok ▸t)
  erase-[] ok (natrecₘ {γ} {δ} {p} {r} {η} ▸t₁ ▸t₂ ▸t₃ _) =
    cong₃ natrec
      (erase-[]
         (λ {x = x} σx≢var-x →
            let x◂𝟘 = ok σx≢var-x in
                                                                      $⟨ x◂𝟘 ⟩
            x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                     →⟨ ◂∈⇔ .proj₁ ⟩

            nrᶜ p r γ δ η ⟨ x ⟩ ≡ 𝟘                                   →⟨ trans (sym (nrᶜ-⟨⟩ γ)) ⟩

            nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≡ 𝟘                  →⟨ trans (update-lookup γ _) ⟩

            (γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)) ⟨ x ⟩ ≡ 𝟘  →⟨ ◂∈⇔ .proj₂ ⟩

            x ◂ 𝟘 ∈ γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)      →⟨ flip x◂𝟘∈γ≤δ $ begin

               γ , x ≔ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)                ≤⟨ update-monotoneʳ _
                                                                                ($⟨ x◂𝟘 ⟩
                 x ◂ 𝟘 ∈ nrᶜ p r γ δ η                                           →⟨ ◂𝟘∈nrᶜ₃ refl ⟩
                 x ◂ 𝟘 ∈ η                                                       →⟨ ◂∈⇔ .proj₁ ⟩
                 η ⟨ x ⟩ ≡ 𝟘                                                     →⟨ nr-zero ∘→ ≤-reflexive ⟩
                 nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≤ γ ⟨ x ⟩                  □) ⟩

               γ , x ≔ γ ⟨ x ⟩                                             ≡⟨ update-self _ _ ⟩

               γ                                                           ∎ ⟩

            x ◂ 𝟘 ∈ γ                                                 □)
         ▸t₁)
      (erase-[] (OK-⇑-∙ $ OK-⇑-∙ $ ◂𝟘∈nrᶜ₂ refl ∘→ ok) ▸t₂)
      (erase-[] (◂𝟘∈nrᶜ₃ refl ∘→ ok) ▸t₃)
    where
    open ≤ᶜ-reasoning
  erase-[] ⦃ 𝟘-well-behaved ⦄ ok (natrec-no-nrₘ ▸t₁ ▸t₂ ▸t₃ _ γ≤₁ _ γ≤₃ γ≤₄) =
    cong₃ natrec (erase-[] ok (sub ▸t₁ γ≤₁))
      (erase-[]
         (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δˡ refl ∘→ flip x◂𝟘∈γ≤δ γ≤₄ ∘→ ok)
         ▸t₂)
      (erase-[] (flip x◂𝟘∈γ≤δ (γ≤₃ λ _ → 𝟘-well-behaved) ∘→ ok) ▸t₃)
  erase-[]
    ok (natrec-no-nr-glbₘ {γ} {δ} {r} {χ} ▸t₁ ▸t₂ ▸t₃ _ glb χ-glb) =
    cong₃ natrec
      (erase-[] (x◂𝟘∈γ+δʳ refl ∘→ ok) $
       sub ▸t₁ $ begin
         χ             ≤⟨ χ-glb .proj₁ 0 ⟩
         nrᵢᶜ r γ δ 0  ≈⟨ nrᵢᶜ-zero ⟩
         γ             ∎)
      (erase-[]
         (OK-⇑-∙ $ OK-⇑-∙ $ x◂𝟘∈γ+δˡ refl ∘→
          flip x◂𝟘∈γ≤δ
            (begin
               χ                       ≤⟨ χ-glb .proj₁ 1 ⟩
               nrᵢᶜ r γ δ 1            ≈⟨ nrᵢᶜ-suc ⟩
               δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ 0  ∎) ∘→
          x◂𝟘∈γ+δʳ refl ∘→ ok)
         ▸t₂)
      (erase-[]
         (x◂𝟘∈pγ refl (λ { refl → 𝟘≰𝟙 (glb .proj₁ 0) }) ∘→
          x◂𝟘∈γ+δˡ refl ∘→ ok)
         ▸t₃)
    where
    open ≤ᶜ-reasoning
  erase-[] _ (Idₘ _ _ _ _) =
    refl
  erase-[] _ (Id₀ₘ _ _ _ _) =
    refl
  erase-[] _ rflₘ =
    refl
  erase-[] ok (Jₘ _ _ _ _ _ ▸t _ _) =
    erase-[]
      (x◂𝟘∈γ+δˡ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→
       x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok)
      ▸t
  erase-[] ok (J₀ₘ₁ _ _ _ _ _ _ ▸t _ _) =
    erase-[] (x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok) ▸t
  erase-[] ok (J₀ₘ₂ _ _ _ _ ▸t _ _) =
    erase-[] ok ▸t
  erase-[] ok (Kₘ _ _ _ _ _ ▸t _) =
    erase-[]
      (x◂𝟘∈γ+δˡ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈γ+δʳ refl ∘→
       x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok)
      ▸t
  erase-[] ok (K₀ₘ₁ _ _ _ _ _ ▸t _) =
    erase-[] (x◂𝟘∈γ+δʳ refl ∘→ x◂𝟘∈pγ refl ω≢𝟘 ∘→ ok) ▸t
  erase-[] ok (K₀ₘ₂ _ _ _ _ ▸t _) =
    erase-[] ok ▸t
  erase-[] _ ([]-congₘ _ _ _ _ _ _) =
    refl

opaque

  -- A variant of erase-[] with a closing substitution.

  wk₀-erase-[] :
    {σ : U.Subst 0 n}
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    T.wk wk₀ (erase′ b s (t U.[ σ ])) ≡ erase′ b s t
  wk₀-erase-[] {t} {b} {s} {σ} ▸t =
    T.wk wk₀ (erase′ b s (t U.[ σ ]))  ≡⟨ wk-erase-comm _ (t U.[ _ ]) ⟩
    erase′ b s (U.wk wk₀ (t U.[ σ ]))  ≡⟨ cong (erase′ _ _) $ UP.wk-subst t ⟩
    erase′ b s (t U.[ wk₀ U.•ₛ σ ])    ≡⟨ erase-[] (λ {x = x} _ → ◂∈⇔ .proj₂ (𝟘ᶜ-lookup x)) ▸t ⟩
    erase′ b s t                       ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A variant of erase-[] stated using ⟨_≔_⟩↑.

  erase-≔↑ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
    erase′ b s (t U.[ ⟨ x ≔ u ⟩↑ ]) ≡ erase′ b s t
  erase-≔↑ x◂ ▸t = erase-[] (flip (lemma _ _) x◂) ▸t
    where
    lemma :
      ∀ (x y : Fin n) {u} →
      ⟨ x ≔ u ⟩↑ y ≢ var y → x ◂ 𝟘 ∈ γ → y ◂ 𝟘 ∈ γ
    lemma x0 x0 _ x◂𝟘 =
      x◂𝟘
    lemma x0 (_ +1) ≢var =
      ⊥-elim $ ≢var refl
    lemma (_+1 {n = 0}    ())
    lemma (_+1 {n = 1+ _} x)  x0 ≢var =
      ⊥-elim $ ≢var refl
    lemma (_+1 {n = 1+ _} x) (y +1) ≢var (there x◂𝟘) =
      there (lemma x y (≢var ∘→ cong U.wk1) x◂𝟘)

opaque

  -- A special case of erase-≔↑.

  erase-[]↑ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    x0 ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
    erase′ b s (t U.[ u ]↑) ≡ erase′ b s t
  erase-[]↑ = erase-≔↑

opaque

  -- A variant of erase-≔↑.

  erase-≔ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
    wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ])) ≡ erase′ b s t
  erase-≔ {x} {t} {b} {s} {u} x◂ ▸t =
    wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ u ⟩ ]))     ≡⟨ wk-erase-comm _ (t U.[ _ ]) ⟩
    erase′ b s (U.wk (step-at x) (t U.[ ⟨ x ≔ u ⟩ ]))   ≡⟨ PE.cong (erase′ _ _) $ UP.wk-subst t ⟩
    erase′ b s (t U.[ step-at x U.•ₛ ⟨ x ≔ u ⟩ ])       ≡⟨⟩
    erase′ b s (t U.[ U.wk (step-at x) ∘→ ⟨ x ≔ u ⟩ ])  ≡⟨ PE.cong (erase′ _ _) $ UP.substVar-to-subst UP.⟨≔⟩≡⟨≔⟩↑ t ⟩
    erase′ b s (t U.[ ⟨ x ≔ U.wk (step-at′ x) u ⟩↑ ])   ≡⟨ erase-≔↑ x◂ ▸t ⟩
    erase′ b s t                                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A special case of erase-≔.

  erase-[]₀ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    x0 ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t →
    T.wk1 (erase′ b s (t U.[ u ]₀)) ≡ erase′ b s t
  erase-[]₀ = erase-≔

opaque

  -- If the modality's zero is well-behaved, then erased variables do
  -- not occur after extraction.

  erased-hasX :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    x ◂ 𝟘 ∈ γ → γ ▸[ 𝟙ᵐ ] t → ¬ HasX x (erase′ b s t)
  erased-hasX {x} {t} {b} {s} x∈ ▸t =
    HasX x (erase′ b s t)                                     →⟨ PE.subst (HasX _) (sym $ erase-≔ x∈ ▸t) ⟩
    HasX x (wk (step-at x) (erase′ b s (t U.[ ⟨ x ≔ ℕ ⟩ ])))  →⟨ ¬-HasX-wk-step-at ⟩
    ⊥                                                         □
