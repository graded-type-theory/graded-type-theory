------------------------------------------------------------------------
-- Weakening properties of Heap typing
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Bool

module Heap.Typed.Weakening
  {a} {M : Set a} {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Weakening TR hiding (wk)
import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Heap.Untyped 𝕄
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Typed TR ℕ-fullred

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n : Nat
  ρ : Wk _ _
  H H′ : Heap _
  c : Closureₘ _ _
  c′ : Closure _ _
  t A B : Term _
  e : Elim _
  S : Stack _
  E : Env _ _
  p : M

private opaque

  wk-liftₕ : (k : Nat) → ρ ∷ H ⊇ʰ H′ → (A : Term _)
           → wk (liftn E k) A [ liftSubstn (toSubstₕ H′) k ] ≡ wk (liftn (ρ • E) k) A [ liftSubstn (toSubstₕ H) k ]
  wk-liftₕ {ρ} {H} {H′} {E} k [ρ] A = begin
    wk (liftn E k) A [ liftSubstn (toSubstₕ H′) k ]      ≡⟨ subst-wk A ⟩
    A [ liftSubstn (toSubstₕ H′) k ₛ• liftn E k ]        ≡⟨ subst-lifts-ₛ• k A ⟩
    A [ liftSubstn (toSubstₕ H′ ₛ• E) k ]                ≡⟨ substVar-to-subst (lemma k) A ⟩
    A [ liftSubstn (toSubstₕ H ₛ• (ρ • E)) k ]           ≡˘⟨ subst-lifts-ₛ• k A ⟩
    A [ liftSubstn (toSubstₕ H) k ₛ• liftn (ρ • E) k ]   ≡˘⟨ subst-wk A ⟩
    wk (liftn (ρ • E) k) A [ liftSubstn (toSubstₕ H) k ] ∎
    where
    lemma : ∀ k x → liftSubstn (toSubstₕ H′ ₛ• E) k x ≡ liftSubstn (toSubstₕ H ₛ• (ρ • E)) k x
    lemma 0 x =
      PE.trans (wk-[]ₕ [ρ] (var (wkVar E x)))
        (cong (toSubstₕ H) (wkVar-comp ρ E x))
    lemma (1+ k) x0 = refl
    lemma (1+ k) (_+1 x) = cong wk1 (lemma k x)

opaque

  -- Weakening of eliminators

  wk-⊢ᵉ : ρ ∷ H ⊇ʰ H′ → H′ ⊢ᵉ e ∷ t ∷ A ↝ B → H ⊢ᵉ wkᵉ ρ e ∷ wk ρ t ∷ A ↝ B
  wk-⊢ᵉ {H} ρ (∘ₑ {E} {u} {B} ⊢u ⊢B) =
    case PE.trans (wk-[]ₕ ρ (wk E u))
           (cong (_[ H ]ₕ) (wk-comp _ E u)) of λ
      u≡u′ →
    case PE.subst (ε ⊢_∷ _) u≡u′ ⊢u of λ
      ⊢u′ →
    subst (H ⊢ᵉ _ ∷ _ ∷ _ ↝_)
      (cong (B [_]₀) (PE.sym u≡u′))
      (∘ₑ ⊢u′ ⊢B)
  wk-⊢ᵉ ρ (fstₑ ⊢A ⊢B) =
    fstₑ ⊢A ⊢B
  wk-⊢ᵉ {ρ} {H} {t} [ρ] (sndₑ {A} {B} {p} {q} ⊢A ⊢B) =
    subst (λ x → H ⊢ᵉ wkᵉ ρ (sndₑ p) ∷ wk ρ t ∷ Σˢ p , q ▷ A ▹ B ↝ B [ x ]₀)
      (PE.sym (wk-[]ₕ [ρ] (fst p t)))
      (sndₑ ⊢A ⊢B)
  wk-⊢ᵉ {ρ} {H} {H′} {t} [ρ] (prodrecₑ {E} {u} {A} ⊢u ⊢A) =
    case wk-liftₕ 1 [ρ] A of λ
      A≡A′ →
    case wk-liftₕ 2 [ρ] u of λ
      u≡u′ →
    case PE.subst₂ (_ ⊢_∷_) u≡u′ (cong (_[ _ ]↑²) A≡A′) ⊢u of λ
      ⊢u′ →
    case PE.subst (λ x → _ ⊢ x) A≡A′ ⊢A of λ
      ⊢A′ →
    subst₂ (λ x y → H ⊢ᵉ _ ∷ _ ∷ _ ↝ (x [ y ]₀))
      (PE.sym A≡A′) (PE.sym (wk-[]ₕ [ρ] t))
      (prodrecₑ ⊢u′ ⊢A′)
  wk-⊢ᵉ {ρ} {H} {H′} {t} [ρ] (natrecₑ {E} {z} {A} {s} {p} {q} {r} ⊢z ⊢s ⊢A) =
    case wk-liftₕ 0 [ρ] z of λ
      z≡z′ →
    case wk-liftₕ 2 [ρ] s of λ
      s≡s′ →
    case wk-liftₕ 1 [ρ] A of λ
      A≡A′ →
    case subst₂ (λ x y → ε ⊢ x ∷ y [ zero ]₀) z≡z′ A≡A′ ⊢z of λ
      ⊢z′ →
    case subst₂ (λ x y → ε ∙ ℕ ∙ x ⊢ y ∷ x [ suc (var x1) ]↑²) A≡A′ s≡s′ ⊢s of λ
      ⊢s′ →
    case subst (λ x → ε ∙ ℕ ⊢ x) A≡A′ ⊢A of λ
      ⊢A′ →
    subst₂ (λ x y → H ⊢ᵉ _ ∷ _ ∷ ℕ ↝ x [ y ]₀)
      (PE.sym A≡A′) (PE.sym (wk-[]ₕ [ρ] t))
      (natrecₑ ⊢z′ ⊢s′ ⊢A′)
  wk-⊢ᵉ {ρ} {H} {H′} {t} [ρ] (unitrecₑ {E} {u} {A} ⊢u ⊢A) =
    case wk-liftₕ 1 [ρ] A of λ
      A≡A′ →
    case subst₂ (ε ⊢_∷_) (wk-liftₕ 0 [ρ] u) (cong _[ starʷ ]₀ A≡A′) ⊢u of λ
      ⊢u′ →
    case subst (λ x → (ε ∙ Unitʷ) ⊢ x) A≡A′ ⊢A of λ
      ⊢A′ →
    subst₂ (λ x y → H ⊢ᵉ _ ∷ _ ∷ _ ↝ (x [ y ]₀))
      (PE.sym A≡A′) (PE.sym (wk-[]ₕ [ρ] t))
      (unitrecₑ ⊢u′ ⊢A′)
  wk-⊢ᵉ {ρ} {H} {t = w} [ρ] (Jₑ {E} {A} {B} {t} {u} {v} {p} {q} ⊢u ⊢B) =
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
    case subst₂ (ε ⊢_∷_) u≡u′ B₊≡B′₊ ⊢u of λ
      ⊢u′ →
    case subst₃ (λ x y z → (ε ∙ x ∙ Id (wk1 x) (wk1 y) (var y0)) ⊢ z)
           A≡A′ t≡t′ B≡B′ ⊢B of λ
      ⊢B′ →
    PE.subst₂ (H ⊢ᵉ Jₑ p q A t B u v (ρ • E) ∷ wk ρ w ∷_↝_)
      (PE.sym (cong₃ Id A≡A′ t≡t′ v≡v′))
      (PE.sym (PE.cong₃ _[_,_]₁₀ B≡B′ v≡v′ (wk-[]ₕ [ρ] w)))
      (Jₑ ⊢u′ ⊢B′)
  wk-⊢ᵉ {ρ} {H} {t = v} [ρ] (Kₑ {E} {u} {B} {A} {t} {p} ⊢u ⊢B ok) =
    case wk-liftₕ 0 [ρ] u of λ
      u≡u′ →
    case wk-liftₕ 1 [ρ] B of λ
      B≡B′ →
    case wk-liftₕ 0 [ρ] (Id A t t) of λ
      Id≡Id′ →
    case subst₂ (ε ⊢_∷_) u≡u′ (cong (_[ rfl ]₀) B≡B′) ⊢u of λ
      ⊢u′ →
    case subst₂ (λ x y → ε ∙ x ⊢ y) Id≡Id′ B≡B′ ⊢B of λ
      ⊢B′ →
    subst₂ (H ⊢ᵉ Kₑ p A t B u (ρ • E) ∷ wk ρ v ∷_↝_)
      (PE.sym Id≡Id′) (PE.sym (cong₂ _[_]₀ B≡B′ (wk-[]ₕ [ρ] v)))
      (Kₑ ⊢u′ ⊢B′ ok)
  wk-⊢ᵉ {ρ} {H} {t = v} [ρ] ([]-congₑ {s′ = s} {A} {t} {u} {E} ok) =
    PE.subst₂ (H ⊢ᵉ []-congₑ s A t u (ρ • E) ∷ wk ρ v ∷_↝_)
      (PE.sym (wk-liftₕ 0 [ρ] (Id A t u)))
      (PE.sym (wk-liftₕ 0 [ρ] (Id (Erased A) ([ t ]) ([ u ])))) ([]-congₑ ok)
    where
    open Erased s
  wk-⊢ᵉ ρ sucₑ = sucₑ
  wk-⊢ᵉ ρ (conv ⊢e x) =
    conv (wk-⊢ᵉ ρ ⊢e) x

opaque

  -- Weakening of stacks

  wk-⊢ˢ : ρ ∷ H ⊇ʰ H′ → H′ ⊢ S ∷ t ∷ A ↝ B → H ⊢ wkˢ ρ S ∷ wk ρ t ∷ A ↝ B
  wk-⊢ˢ ρ ε = ε
  wk-⊢ˢ {ρ} {H} {H′} {S = e ∙ S} {t} [ρ] (⊢e ∙ ⊢S) =
      wk-⊢ᵉ [ρ] ⊢e
    ∙ PE.subst (H ⊢ wkˢ ρ S ∷_∷ _ ↝ _) (wk-⦅⦆ᵉ e) (wk-⊢ˢ [ρ] ⊢S)
