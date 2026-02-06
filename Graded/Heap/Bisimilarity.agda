------------------------------------------------------------------------
-- Bisimilarity properties between the different semantics of the
-- abstract machine and the weak head reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Bisimilarity
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  (TR : Type-restrictions 𝕄)
  (∣ε∣ : M)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
import Tools.Level as L
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

open import Graded.Heap.Assumptions UR TR ∣ε∣

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR hiding (_⇨*_)
open import Definition.Typed.Well-formed TR

open import Graded.Context 𝕄 hiding (_⟨_⟩)

private variable
  t t′ u u′ v w A B : Term _
  ρ ρ′ : Wk _ _
  γ δ η : Conₘ _
  Γ Δ : Con Term _
  l : Universe-level
  p q : M

private
  module Imports
    (factoring-nr :
      ⦃ has-nr : Nr-available ⦄ →
      Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
    where
    open import Graded.Heap.Untyped              type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Untyped.Properties   type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Usage                type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Usage.Inversion      type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Usage.Properties     type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Normalization        type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Reduction            type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr ∣ε∣ public
    open import Graded.Heap.Typed                          UR TR factoring-nr ∣ε∣ public
    open import Graded.Heap.Typed.Inversion                UR TR factoring-nr ∣ε∣ public
    open import Graded.Heap.Typed.Properties               UR TR factoring-nr ∣ε∣ public
    open import Graded.Heap.Typed.Reduction                UR TR factoring-nr ∣ε∣ public

    variable
      s s′ : State _ _ _
      H H′ H″ : Heap _ _
      S S′ S″ : Stack _

------------------------------------------------------------------------
-- Bisimilarity between the tracking and non-tracking semantics.

-- These first direction is proven under the assumption that the nr
-- function is factoring (if it is used for usage).

module _
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

  open Imports factoring-nr

  opaque

    ⇾ₑ→⇢ₑ : s ⇾ₑ ⟨ H , t , ρ , S ⟩
          → ∃ λ H′ → s ⇢ₑ ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
    ⇾ₑ→⇢ₑ (var _ d) = _ , var (↦[]→↦ d) , ~ʰ-sym (update-~ʰ d)
    ⇾ₑ→⇢ₑ (⇒ₑ d) = _ , ⇒ₑ d , ~ʰ-refl

  opaque

    ⇾→⇢ : s ⇾ ⟨ H , t , ρ , S ⟩
        → ∃ λ H′ → s ⇢ ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
    ⇾→⇢ (⇾ₑ d) =
      let _ , d′ , H~H′ = ⇾ₑ→⇢ₑ d
      in  _ , ⇢ₑ d′ , H~H′
    ⇾→⇢ (⇒ᵥ d) = _ , ⇒ᵥ d , ~ʰ-refl

  opaque

    ⇾*→⇢* : s ⇾* ⟨ H , t , ρ , S ⟩
          → ∃ λ H′ → s ⇢* ⟨ H′ , t , ρ , S ⟩ × H ~ʰ H′
    ⇾*→⇢* id = _ , id , ~ʰ-refl
    ⇾*→⇢* (_⇨_ {s₂ = record{}} x d) =
      let _ , x′ , H~H′ = ⇾→⇢ x
          _ , d′ , H~H″ = ⇾*→⇢* d
          _ , d″ , H~H‴ = ~ʰ-⇢* d′ H~H′
      in  _ , x′ ⇨ d″ , ~ʰ-trans H~H″ H~H‴

-- The other direction is proven under some additional assumptions

module _ (As : Assumptions) where

  open Assumptions As
  open Imports factoring-nr
  open import Graded.Heap.Usage.Reduction
    type-variant UR factoring-nr ∣ε∣ Unitʷ-η→ ¬Nr-not-available

  opaque

    ⇢ₑ→⇾ₑ :
      H ~ʰ H″ → ▸ ⟨ H″ , t , ρ , S ⟩ →
      ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩ →
      ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾ₑ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢ₑ→⇾ₑ H~H″ ▸s (var d) =
      let _ , _ , _ , _ , ∣S∣≡ , _ = ▸ₛ-inv ▸s
          H , d′ = ▸↦→↦[] subtraction-ok ∣S∣≡ (~ʰ-lookup H~H″ d) ▸s
      in  _ , var ∣S∣≡ d′ , ~ʰ-trans H~H″ (update-~ʰ d′)
    ⇢ₑ→⇾ₑ H~H″ _ (⇒ₑ d) =
      let _ , d′ , H′~H‴ = ~ʰ-⇒ₑ d H~H″
      in  _ , ⇒ₑ d′ , H′~H‴

  opaque

    ⇢ₑ*→⇾ₑ* :
      H ~ʰ H″ → ▸ ⟨ H″ , t , ρ , S ⟩ →
      ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ⟩ →
      ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾ₑ* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢ₑ*→⇾ₑ* H~H″ ▸s id = _ , id , H~H″
    ⇢ₑ*→⇾ₑ* H~H″ ▸s (_⇨_ {s′ = record{}} x d) =
      let _ , x′ , H~H′ = ⇢ₑ→⇾ₑ H~H″ ▸s x
          ▸s′ = ▸-⇾ₑ ▸s x′
          _ , d′ , H~H‴ = ⇢ₑ*→⇾ₑ* H~H′ ▸s′ d
      in  _ , x′ ⇨ d′ , H~H‴

  opaque

    ⇢→⇾ :
      H ~ʰ H″ → ▸ ⟨ H″ , t , ρ , S ⟩ →
      ⟨ H , t , ρ , S ⟩ ⇢ ⟨ H′ , t′ , ρ′ , S′ ⟩ →
      ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢→⇾ H~H″ ▸s (⇢ₑ d) =
      let _ , d′ , H~H′ = ⇢ₑ→⇾ₑ H~H″ ▸s d
      in  _ , ⇾ₑ d′ , H~H′
    ⇢→⇾ H~H″ ▸s (⇒ᵥ d) =
      let _ , d′ , H~H′ = ~ʰ-⇒ᵥ d H~H″
      in  _ , ⇒ᵥ d′ , H~H′

  opaque

    ⇢*→⇾* :
      H ~ʰ H″ → ▸ ⟨ H″ , t , ρ , S ⟩ →
      ⟨ H , t , ρ , S ⟩ ⇢* ⟨ H′ , t′ , ρ′ , S′ ⟩ →
      ∃ λ H‴ → ⟨ H″ , t , ρ , S ⟩ ⇾* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H′ ~ʰ H‴
    ⇢*→⇾* H~H″ ▸s id =
      _ , id , H~H″
    ⇢*→⇾* H~H″ ▸s (_⇨_ {s₂ = record{}} x d) =
      let _ , x′ , H~H′ = ⇢→⇾ H~H″ ▸s x
          _ , d′ , H~H‴ = ⇢*→⇾* H~H′ (▸-⇾ ▸s x′) d
      in  _ , x′ ⇨ d′ , H~H‴

  opaque

    -- Normalization for the tracking semantics

    ▸normalize :
      ∀ {k m n} (s : State k m n) → No-namesₛ′ s → ▸ s →
      ∃₂ λ n′ (s′ : State _ _ n′) → Normal s′ × s ⇾ₑ* s′
    ▸normalize s@record{} s-nn ▸s =
      let (_ , record{} , n , d) = normalizeₛ s s-nn
          _ , d′ , H~H′ = ⇢ₑ*→⇾ₑ* ~ʰ-refl ▸s d
      in  _ , _ , ~ʰ-Normal H~H′ n , d′

  opaque

    -- A variant of the above

    ▸⊢normalize :
      ∀ {k m n} {Δ : Con Term k} {A : Term k} →
      (s : State k m n) → ▸ s → Δ ⊢ₛ s ∷ A →
      ∃₂ λ n′ (s′ : State _ _ n′) → Normal s′ × s ⇾ₑ* s′
    ▸⊢normalize s ▸s ⊢s =
      ▸normalize s (⊢ₛ→No-namesₛ′ ⊢s) ▸s

------------------------------------------------------------------------
-- Bisimilarity between the weak head call-by-name reduction and
-- the abstract machine (with tracking).

-- Most properties are proven under the assumptions that the nr
-- function is factoring (if it is used for usage), that equality
-- reflection is not allowed or the context is empty, and that Level
-- is not allowed.

module _
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  ⦃ ok : No-equality-reflection or-empty Δ ⦄
  (Level-not-allowed : ¬ Level-allowed)
  where

  open Imports factoring-nr

  opaque

    ⇾→⊢⇒ : Δ ⊢ₛ s ∷ A → s ⇾ s′ → ε » Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
    ⇾→⊢⇒ {s} ⊢s (⇾ₑ d) =
      subst (_ ⊢ _ ⇒*_∷ _) (⇾ₑ-⦅⦆-≡ d) (id (⊢⦅⦆ {s = s} ⊢s))
    ⇾→⊢⇒ ⊢s (⇒ᵥ d) =
      redMany (⇒ᵥ→⇒ ⊢s d)

  opaque

    ⇾*→⊢⇒* : Δ ⊢ₛ s ∷ A → s ⇾* s′ → ε » Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
    ⇾*→⊢⇒* {s} ⊢s id = id (⊢⦅⦆ {s = s} ⊢s)
    ⇾*→⊢⇒* {s = record{}} ⊢s (_⇨_ {s₂ = record{}} x d) =
      ⇾→⊢⇒ ⊢s x ⇨∷* ⇾*→⊢⇒* (⊢ₛ-⇾ ⊢s x) d

  opaque

    ⊢⇒→⇒ᵥ : ε » Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A
          → Normal s
          → Δ ⊢ₛ s ∷ B
          → ∣ State.stack s ∣≡ p
          → ∃₃ λ m n (s′ : State _ m n) → s ⇒ᵥ s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒→⇒ᵥ {s = ⟨ H , t , ρ , ε ⟩} d (val x) ⊢s _ =
      case Value→Whnf (substValue (toSubstₕ H) (wkValue ρ x)) of λ where
          (inj₁ w) → ⊥-elim (whnfRedTerm d w)
          (inj₂ (_ , _ , _ , _ , _ , ≡ur , η)) →
            case subst-unitrec {t = wk ρ t} ≡ur of λ where
              (inj₁ (_ , ≡x)) → case subst Value ≡x (wkValue ρ x) of λ ()
              (inj₂ (_ , _ , _ , ≡ur′ , refl , refl , refl)) →
                case wk-unitrec ≡ur′ of λ {
                  (_ , _ , _ , refl , refl , refl , refl) →
                _ , _ , _ , unitrec-ηₕ η , lemma η d}
        where
        lemma :
          Unitʷ-η → ε » Δ ⊢ (unitrec p q A u v) ⇒ w ∷ B → w PE.≡ v
        lemma η (conv d x) = lemma η d
        lemma η (unitrec-subst _ _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β-η _ _ _ _ _) = refl
    ⊢⇒→⇒ᵥ {s = ⟨ H , t , ρ , e ∙ S ⟩} d (val v) ⊢s ∣S∣≡ =
      case ⊢Value-⇒ᵥ ∣S∣≡ ⊢s v of λ
        (_ , _ , _ , d′) →
      _ , _ , _ , d′ , whrDetTerm d (⇒ᵥ→⇒ ⊢s d′)
    ⊢⇒→⇒ᵥ d (var d′) ⊢s - =
      let _ , _ , _ , _ , ⊢S = ⊢ₛ-inv ⊢s
      in  ⊥-elim $ neRedTerm {V = L.Lift _ ⊤} d $ NeutralAt→Neutral $
          toSubstₕ-NeutralAt d′ $ ⊢⦅⦆ˢ-NeutralAt ⊢S (var _)
    ⊢⇒→⇒ᵥ _ sup (⊢ₛ _ ⊢supᵘ _) - =
      ⊥-elim $ Level-not-allowed $
      inversion-Level-⊢ (wf-⊢∷ (inversion-supᵘ ⊢supᵘ .proj₁))

-- The remaining properties are proven under some additional assumptions

module _ (As : Assumptions) where

  open Assumptions As
  open Imports factoring-nr
  open import Graded.Heap.Usage.Reduction
    type-variant UR factoring-nr ∣ε∣ Unitʷ-η→ ¬Nr-not-available

  opaque

    ⊢⇒→⇾* :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ε » Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ∃₃ λ m n (s′ : State _ m n) → s ⇾* s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒→⇾* {s} d ⊢s ▸s =
      case ▸⊢normalize As s ▸s ⊢s of λ {
        (_ , record{} , n , d′) →
      let d″ = PE.subst (_ ⊢_⇒ _ ∷ _) (⇾ₑ*-⦅⦆-≡ d′) d
          ⊢s′ = ⊢ₛ-⇾ₑ* ⊢s d′
          _ , _ , _ , _ , ∣S∣≡ , _ = ▸ₛ-inv (▸-⇾ₑ* ▸s d′)
          _ , _ , s″ , d‴ , u≡ =
            ⊢⇒→⇒ᵥ factoring-nr Level-not-allowed d″ n ⊢s′ ∣S∣≡
      in  _ , _ , s″ , ⇾ₑ* d′ ⇨* ⇒ᵥ d‴ ⇨ id , u≡ }

  opaque

    ⊢⇒*→⇾* :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      ε » Δ ⊢ ⦅ s ⦆ ⇒* u ∷ A →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ∃₃ λ m n (s′ : State _ m n) → s ⇾* s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒*→⇾* (id x) ⊢s ▸s =
      _ , _ , _ , id , refl
    ⊢⇒*→⇾* {s} (x ⇨ d) ⊢s ▸s =
      case ⊢⇒→⇾* {s = s} x ⊢s ▸s of λ {
        (_ , _ , _ , x′ , refl) →
      case ⊢ₛ-⇾* ⊢s x′ of λ
        ⊢s′ →
      case ▸-⇾* ▸s x′ of λ
        ▸s′ →
      case ⊢⇒*→⇾* d ⊢s′ ▸s′ of λ
        (_ , _ , s′ , d′ , u≡) →
      _ , _ , s′ , x′ ⇨* d′ , u≡ }

  opaque

    -- A variant of the above for reduction to Whnf

    ↘→⇘ :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ε » Δ ⊢ ⦅ s ⦆ ↘ u ∷ A →
      ∃₃ λ m n (s′ : State _ m n) → s ⇘ s′ × u ≡ ⦅ s′ ⦆
    ↘→⇘ ⊢s ▸s (d , w) =
      let _ , _ , s′ , d₁ , u≡ = ⊢⇒*→⇾* d ⊢s ▸s
          ▸s′ = ▸-⇾* ▸s d₁
          ⊢s′ = ⊢ₛ-⇾* ⊢s d₁
          _ , s″ , n , d₂ =
            ▸⊢normalize As s′ ▸s′ ⊢s′
          d′ = d₁ ⇨* ⇾ₑ* d₂
          ⊢s″ = ⊢ₛ-⇾* ⊢s d′
          u≡′ = PE.trans u≡ (⇾ₑ*-⦅⦆-≡ d₂)
          w′ = subst (Whnf _) u≡′ w
      in  _ , _ , s″
            , (d′ , λ d″ → whnfRedTerm (⇒ᵥ→⇒ ⊢s″ (Normal-⇾→⇒ᵥ n d″)) w′)
            , u≡′
