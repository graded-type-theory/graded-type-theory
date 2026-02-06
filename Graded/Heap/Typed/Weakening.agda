------------------------------------------------------------------------
-- Weakening properties of Heap typing
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Weakening
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  (TR : Type-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open Type-restrictions TR

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M
open import Definition.Typed TR

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Typed UR TR factoring-nr ∣ε∣

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n : Nat
  ρ ρ′ : Wk _ _
  Δ : Con Term _
  H H′ : Heap _ _
  t A B : Term _
  c : Cont _
  S : Stack _
  p : M

private opaque

  wk-liftₕ : (k : Nat) → ρ ∷ H ⊇ʰ H′ → (A : Term _)
           → wk (liftn ρ′ k) A [ liftSubstn (toSubstₕ H′) k ] ≡ wk (liftn (ρ • ρ′) k) A [ liftSubstn (toSubstₕ H) k ]
  wk-liftₕ {ρ} {H} {H′} {ρ′} k [ρ] A = begin
    wk (liftn ρ′ k) A [ liftSubstn (toSubstₕ H′) k ]      ≡⟨ subst-wk A ⟩
    A [ liftSubstn (toSubstₕ H′) k ₛ• liftn ρ′ k ]        ≡⟨ subst-lifts-ₛ• k A ⟩
    A [ liftSubstn (toSubstₕ H′ ₛ• ρ′) k ]                ≡⟨ substVar-to-subst (lemma k) A ⟩
    A [ liftSubstn (toSubstₕ H ₛ• (ρ • ρ′)) k ]           ≡˘⟨ subst-lifts-ₛ• k A ⟩
    A [ liftSubstn (toSubstₕ H) k ₛ• liftn (ρ • ρ′) k ]   ≡˘⟨ subst-wk A ⟩
    wk (liftn (ρ • ρ′) k) A [ liftSubstn (toSubstₕ H) k ] ∎
    where
    lemma : ∀ k x → liftSubstn (toSubstₕ H′ ₛ• ρ′) k x ≡ liftSubstn (toSubstₕ H ₛ• (ρ • ρ′)) k x
    lemma 0 x =
      PE.trans (wk-[]ₕ [ρ] (var (wkVar ρ′ x)))
        (cong (toSubstₕ H) (wkVar-comp ρ ρ′ x))
    lemma (1+ k) x0 = refl
    lemma (1+ k) (_+1 x) = cong wk1 (lemma k x)

opaque

  -- Weakening of continuations

  wk-⊢ᶜ : ρ ∷ H ⊇ʰ H′ → Δ ⨾ H′ ⊢ᶜ c ⟨ t ⟩∷ A ↝ B → Δ ⨾ H ⊢ᶜ wkᶜ ρ c ⟨ wk ρ t ⟩∷ A ↝ B
  wk-⊢ᶜ ρ (lowerₑ ⊢B) =
    lowerₑ ⊢B
  wk-⊢ᶜ {ρ} {H} {Δ} {t} [ρ] (∘ₑ {ρ = ρ′} {u} {A} {B} {p} ⊢u ⊢B) =
    case wk-liftₕ 0 [ρ] u of λ
      u≡u′ →
    case PE.subst (_ ⊢_∷ _) u≡u′ ⊢u of λ
      ⊢u′ →
    subst (Δ ⨾ H ⊢ᶜ ∘ₑ p u (ρ • ρ′) ⟨ wk ρ t ⟩∷ _ ↝_)
      (cong (B [_]₀) (PE.sym u≡u′)) (∘ₑ ⊢u′ ⊢B)
  wk-⊢ᶜ ρ (fstₑ ⊢B) =
    fstₑ ⊢B
  wk-⊢ᶜ {ρ} {H} {Δ} {t} [ρ] (sndₑ {A} {B} {p} {q} ⊢B) =
    subst (λ x → Δ ⨾ H ⊢ᶜ wkᶜ ρ (sndₑ p) ⟨ wk ρ t ⟩∷ Σˢ p , q ▷ A ▹ B ↝ B [ x ]₀)
      (PE.sym (wk-[]ₕ [ρ] (fst p t)))
      (sndₑ ⊢B)
  wk-⊢ᶜ {ρ} {H} {H′} {Δ} {t} [ρ] (prodrecₑ {ρ = ρ′} {u} {A} {p} {r} {q} ⊢u ⊢A) =
    case wk-liftₕ 1 [ρ] A of λ
      A≡A′ →
    case wk-liftₕ 2 [ρ] u of λ
      u≡u′ →
    case PE.subst₂ (_ ⊢_∷_) u≡u′ (cong (_[ _ ]↑²) A≡A′)
           ⊢u of λ
      ⊢u′ →
    case PE.subst (_⊢_ _) A≡A′ ⊢A of λ
      ⊢A′ →
    subst (Δ ⨾ H ⊢ᶜ prodrecₑ r p q A u (ρ • ρ′) ⟨ wk ρ t ⟩∷ _ ↝_)
      (PE.sym (cong₂ _[_]₀ A≡A′ (wk-[]ₕ [ρ] t))) (prodrecₑ ⊢u′ ⊢A′)
  wk-⊢ᶜ {ρ} {H} {H′} {t} [ρ] (natrecₑ {z} {A} {s} ⊢z ⊢s) =
    case wk-liftₕ 0 [ρ] z of λ
      z≡z′ →
    case wk-liftₕ 2 [ρ] s of λ
      s≡s′ →
    case wk-liftₕ 1 [ρ] A of λ
      A≡A′ →
    case subst₂ (λ x y → _ ⊢ x ∷ y [ zero ]₀) z≡z′ A≡A′ ⊢z of λ
      ⊢z′ →
    case subst₂ (λ x y → _ » _ ∙ _ ∙ x ⊢ y ∷ x [ suc (var x1) ]↑²)
           A≡A′ s≡s′ ⊢s of λ
      ⊢s′ →
    subst₂ (λ x y → _ ⨾ H ⊢ᶜ _ ⟨ _ ⟩∷ ℕ ↝ x [ y ]₀)
      (PE.sym A≡A′) (PE.sym (wk-[]ₕ [ρ] t))
      (natrecₑ ⊢z′ ⊢s′)
  wk-⊢ᶜ {ρ} {H} {H′} {t} [ρ] (unitrecₑ {u} {A} ⊢u ⊢A no-η) =
    case wk-liftₕ 1 [ρ] A of λ
      A≡A′ →
    case subst₂ (_ ⊢_∷_) (wk-liftₕ 0 [ρ] u) (cong _[ _ ]₀ A≡A′) ⊢u of λ
      ⊢u′ →
    case subst (_⊢_ _) A≡A′ ⊢A of λ
      ⊢A′ →
    subst₂ (λ x y → _ ⨾ H ⊢ᶜ _ ⟨ _ ⟩∷ _ ↝ (x [ y ]₀))
      (PE.sym A≡A′) (PE.sym (wk-[]ₕ [ρ] t))
      (unitrecₑ ⊢u′ ⊢A′ no-η)
  wk-⊢ᶜ {ρ} {H} {H′} {t} [ρ] (emptyrecₑ {A} ⊢A) =
    case wk-liftₕ 0 [ρ] A of λ
      A≡A′ →
    case subst (λ x → _ ⊢ x) A≡A′ ⊢A of λ
      ⊢A′ →
    subst (_ ⨾ H ⊢ᶜ _ ⟨ _ ⟩∷ _ ↝_)
      (PE.sym A≡A′) (emptyrecₑ ⊢A′)
  wk-⊢ᶜ {ρ} {H} {Δ} {t = w} [ρ] (Jₑ {ρ = ρ′} {A} {B} {t} {u} {v} {p} {q} ⊢u ⊢B) =
    case wk-liftₕ 0 [ρ] u of λ
      u≡u′ →
    case wk-liftₕ 2 [ρ] B of λ
      B≡B′ →
    case wk-liftₕ 0 [ρ] A of λ
      A≡A′ →
    case wk-liftₕ 0 [ρ] t of λ
      t≡t′ →
    case wk-liftₕ 0 [ρ] v of λ
      v≡v′ →
    case cong₂ (λ x y → x [ y , rfl ]₁₀) B≡B′ t≡t′ of λ
      B₊≡B′₊ →
    case subst₂ (_ ⊢_∷_) u≡u′ B₊≡B′₊ ⊢u of λ
      ⊢u′ →
    case subst₃ (λ x y z → _ » _ ∙ x ∙ Id (wk1 x) (wk1 y) _ ⊢ z)
           A≡A′ t≡t′ B≡B′ ⊢B of λ
      ⊢B′ →
    PE.subst₂ (Δ ⨾ H ⊢ᶜ Jₑ p q A t B u v (ρ • ρ′) ⟨ wk ρ w ⟩∷_↝_)
      (PE.sym (cong₃ Id A≡A′ t≡t′ v≡v′))
      (PE.sym (PE.cong₃ _[_,_]₁₀ B≡B′ v≡v′ (wk-[]ₕ [ρ] w)))
      (Jₑ ⊢u′ ⊢B′)
  wk-⊢ᶜ {ρ} {H} {Δ} {t = v} [ρ] (Kₑ {ρ = ρ′} {u} {B} {A} {t} {p} ⊢u ⊢B ok) =
    case wk-liftₕ 0 [ρ] u of λ
      u≡u′ →
    case wk-liftₕ 1 [ρ] B of λ
      B≡B′ →
    case wk-liftₕ 0 [ρ] (Id A t t) of λ
      Id≡Id′ →
    case subst₂ (_ ⊢_∷_) u≡u′ (cong (_[ rfl ]₀) B≡B′) ⊢u of λ
      ⊢u′ →
    case subst₂ (λ x y → ε » Δ ∙ x ⊢ y) Id≡Id′ B≡B′ ⊢B of λ
      ⊢B′ →
    subst₂ (Δ ⨾ H ⊢ᶜ Kₑ p A t B u (ρ • ρ′) ⟨ wk ρ v ⟩∷_↝_)
      (PE.sym Id≡Id′) (PE.sym (cong₂ _[_]₀ B≡B′ (wk-[]ₕ [ρ] v)))
      (Kₑ ⊢u′ ⊢B′ ok)
  wk-⊢ᶜ
    {ρ} {H} {Δ} {t = v}
    [ρ] ([]-congₑ {s′ = s} {ρ = ρ′} {l} {A} {t} {u} ok ⊢l) =
    PE.subst₂ (Δ ⨾ H ⊢ᶜ []-congₑ s l A t u (ρ • ρ′) ⟨ wk ρ v ⟩∷_↝_)
      (PE.sym (wk-liftₕ 0 [ρ] (Id A t u)))
      (PE.sym (wk-liftₕ 0 [ρ] (Id (Erased l A) ([ t ]) ([ u ]))))
      ([]-congₑ ok (subst (_⊢_∷Level _) (wk-liftₕ 0 [ρ] l) ⊢l))
    where
    open Erased s
  wk-⊢ᶜ ρ (conv ⊢c x) =
    conv (wk-⊢ᶜ ρ ⊢c) x

opaque

  -- Weakening of stacks

  wk-⊢ˢ : ρ ∷ H ⊇ʰ H′ → Δ ⨾ H′ ⊢ S ⟨ t ⟩∷ A ↝ B → Δ ⨾ H ⊢ wkˢ ρ S ⟨ wk ρ t ⟩∷ A ↝ B
  wk-⊢ˢ ρ ε = ε
  wk-⊢ˢ {ρ} {H} {H′} {S = c ∙ S} {t} [ρ] (⊢c ∙ ⊢S) =
      wk-⊢ᶜ [ρ] ⊢c
    ∙ PE.subst (_ ⨾ H ⊢ wkˢ ρ S ⟨_⟩∷ _ ↝ _) (wk-⦅⦆ᶜ c) (wk-⊢ˢ [ρ] ⊢S)
