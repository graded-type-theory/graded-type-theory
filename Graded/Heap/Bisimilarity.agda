------------------------------------------------------------------------
-- Bisimilarity properties between the different semantics of the
-- abstract machine and the weak head reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Bisimilarity
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Sum

open import Graded.Heap.Assumptions UR TR

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties.Neutral M type-variant

open import Definition.Typed TR
open import Definition.Typed.Properties TR hiding (_⇨*_)

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
    open import Graded.Heap.Untyped              type-variant UR factoring-nr public
    open import Graded.Heap.Untyped.Properties   type-variant UR factoring-nr public
    open import Graded.Heap.Usage                type-variant UR factoring-nr public
    open import Graded.Heap.Usage.Inversion      type-variant UR factoring-nr public
    open import Graded.Heap.Usage.Properties     type-variant UR factoring-nr public
    open import Graded.Heap.Normalization        type-variant UR factoring-nr public
    open import Graded.Heap.Reduction            type-variant UR factoring-nr public
    open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr public
    open import Graded.Heap.Typed                          UR TR factoring-nr public
    open import Graded.Heap.Typed.Inversion                UR TR factoring-nr public
    open import Graded.Heap.Typed.Properties               UR TR factoring-nr public
    open import Graded.Heap.Typed.Reduction                UR TR factoring-nr public

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
          → ∃₂ λ H′ S′ → s ⇢ₑ ⟨ H′ , t , ρ , S′ ⟩ × H ~ʰ H′ × S ~ˢ S′
    ⇾ₑ→⇢ₑ (var d) = _ , _ , var (↦[]→↦ d) , ~ʰ-sym (update-~ʰ d) , ~ˢ-refl
    ⇾ₑ→⇢ₑ (⇒ₑ d) = _ , _ , ⇒ₑ d , ~ʰ-refl , ~ˢ-refl
    ⇾ₑ→⇢ₑ (natrecₕ ok) = _ , _ , natrecₕ , ~ʰ-refl , ~ᵉ-natrec ∙ ~ˢ-refl

  opaque

    ⇾→⇢ : s ⇾ ⟨ H , t , ρ , S ⟩
        → ∃₂ λ H′ S′ → s ⇢ ⟨ H′ , t , ρ , S′ ⟩ × H ~ʰ H′ × S ~ˢ S′
    ⇾→⇢ (⇾ₑ d) =
      let _ , _ , d′ , H~H′ , S~S′ = ⇾ₑ→⇢ₑ d
      in  _ , _ , ⇢ₑ d′ , H~H′ , S~S′
    ⇾→⇢ (⇒ᵥ d) = _ , _ , ⇒ᵥ d , ~ʰ-refl , ~ˢ-refl

  opaque

    ⇾*→⇢* : s ⇾* ⟨ H , t , ρ , S ⟩
          → ∃₂ λ H′ S′ → s ⇢* ⟨ H′ , t , ρ , S′ ⟩ × H ~ʰ H′ × S ~ˢ S′
    ⇾*→⇢* id = _ , _ , id , ~ʰ-refl , ~ˢ-refl
    ⇾*→⇢* (_⇨_ {s₂ = record{}} x d) =
      let _ , _ , x′ , H~H′ , S~S′ = ⇾→⇢ x
          _ , _ , d′ , H~H″ , S~S″ = ⇾*→⇢* d
          _ , _ , d″ , H~H‴ , S~S‴ = ~ʰ-~ˢ-⇢* d′ H~H′ S~S′
      in  _ , _ , x′ ⇨ d″ , ~ʰ-trans H~H″ H~H‴ , ~ˢ-trans S~S″ S~S‴

-- The other direction is proven under some additional assumptions

module _ (As : Assumptions) where

  open Assumptions As
  open Imports factoring-nr
  open import Graded.Heap.Usage.Reduction type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available

  opaque

    ⇢ₑ→⇾ₑ : H ~ʰ H″ → S ~ˢ S″
          → ▸ ⟨ H″ , t , ρ , S″ ⟩
          → ⟨ H , t , ρ , S ⟩ ⇢ₑ ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ∃₂ λ H‴ S‴ → ⟨ H″ , t , ρ , S″ ⟩ ⇾ₑ ⟨ H‴ , t′ , ρ′ , S‴ ⟩ × H′ ~ʰ H‴ × S′ ~ˢ S‴
    ⇢ₑ→⇾ₑ H~H″ S~S″ ▸s (var d) =
      let H , d′ = ▸↦→↦[] subtraction-ok (~ʰ-lookup H~H″ d) ▸s
      in  _ , _ , var d′ , ~ʰ-trans H~H″ (update-~ʰ d′) , S~S″
    ⇢ₑ→⇾ₑ H~H″ S~S″ _ (⇒ₑ d) =
      let _ , _ , d′ , H′~H‴ , S′~S‴ = ~ʰ-~ˢ-⇒ₑ d H~H″ S~S″
      in  _ , _ , ⇒ₑ d′ , H′~H‴ , S′~S‴
    ⇢ₑ→⇾ₑ H~H″ S~S″ ▸s natrecₕ =
      let _ , _ , _ , _ , ▸natrec , _ = ▸ₛ-inv ▸s
      in  _ , _ , natrecₕ (▸natrec→Ok-nr ¬Nr-not-available ▸natrec .proj₂)
            , H~H″ , (~ᵉ-natrec ∙ S~S″)

  opaque

    ⇢ₑ*→⇾ₑ* : H ~ʰ H″ → S ~ˢ S″
            → ▸ ⟨ H″ , t , ρ , S″ ⟩
            → ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H′ , t′ , ρ′ , S′ ⟩
            → ∃₂ λ H‴ S‴ → ⟨ H″ , t , ρ , S″ ⟩ ⇾ₑ* ⟨ H‴ , t′ , ρ′ , S‴ ⟩ × H′ ~ʰ H‴ × S′ ~ˢ S‴
    ⇢ₑ*→⇾ₑ* H~H″ S~S″ ▸s id = _ , _ , id , H~H″ , S~S″
    ⇢ₑ*→⇾ₑ* H~H″ S~S″ ▸s (_⇨_ {s′ = record{}} x d) =
      let _ , _ , x′ , H~H′ , S~S′ = ⇢ₑ→⇾ₑ H~H″ S~S″ ▸s x
          ▸s′ = ▸-⇾ₑ ▸s x′
          _ , _ , d′ , H~H‴ , S~S‴ = ⇢ₑ*→⇾ₑ* H~H′ S~S′ ▸s′ d
      in  _ , _ , x′ ⇨ d′ , H~H‴ , S~S‴

  opaque

    ⇢→⇾ : H ~ʰ H″ → S ~ˢ S″
        → ▸ ⟨ H″ , t , ρ , S″ ⟩
        → ⟨ H , t , ρ , S ⟩ ⇢ ⟨ H′ , t′ , ρ′ , S′ ⟩
        → ∃₂ λ H‴ S‴ → ⟨ H″ , t , ρ , S″ ⟩ ⇾ ⟨ H‴ , t′ , ρ′ , S‴ ⟩ × H′ ~ʰ H‴ × S′ ~ˢ S‴
    ⇢→⇾ H~H″ S~S″ ▸s (⇢ₑ d) =
      let _ , _ , d′ , H~H′ , S~S′ = ⇢ₑ→⇾ₑ H~H″ S~S″ ▸s d
      in  _ , _ , ⇾ₑ d′ , H~H′ , S~S′
    ⇢→⇾ H~H″ S~S″ ▸s (⇒ᵥ d) =
      let _ , _ , d′ , H~H′ , S~S′ = ~ʰ-~ˢ-⇒ᵥ d H~H″ S~S″
      in  _ , _ , ⇒ᵥ d′ , H~H′ , S~S′

  opaque

    ⇢*→⇾* : H ~ʰ H″ → S ~ˢ S″
          → ▸ ⟨ H″ , t , ρ , S″ ⟩
          → ⟨ H , t , ρ , S ⟩ ⇢* ⟨ H′ , t′ , ρ′ , S′ ⟩
          → ∃₂ λ H‴ S‴ → ⟨ H″ , t , ρ , S″ ⟩ ⇾* ⟨ H‴ , t′ , ρ′ , S‴ ⟩ × H′ ~ʰ H‴ × S′ ~ˢ S‴
    ⇢*→⇾* H~H″ S~S″ ▸s id =
      _ , _ , id , H~H″ , S~S″
    ⇢*→⇾* H~H″ S~S″ ▸s (_⇨_ {s₂ = record{}} x d) =
      let _ , _ , x′ , H~H′ , S~S′ = ⇢→⇾ H~H″ S~S″ ▸s x
          _ , _ , d′ , H~H‴ , S~S‴  = ⇢*→⇾* H~H′ S~S′ (▸-⇾ ▸s x′) d
      in  _ , _ , x′ ⇨ d′ , H~H‴ , S~S‴

  opaque

    -- Normalization for the tracking semantics

    ▸normalize : ∀ {k m n} (s : State k m n) → ▸ s
               → ∃₂ λ n′ (s′ : State _ _ n′) → Normal s′ × s ⇾ₑ* s′
    ▸normalize s@record{} ▸s with normalizeₛ s
    … | _ , record{} , n , d =
      let _ , _ , d′ , H~H′ , _ = ⇢ₑ*→⇾ₑ* ~ʰ-refl ~ˢ-refl ▸s d
      in  _ , _ , ~ʰ-Normal H~H′ n , d′

------------------------------------------------------------------------
-- Bisimilarity between the weak head call-by-name reduction and
-- the abstract machine (with tracking).

-- Most properties are proven under the assumptions that the nr
-- function is factoring (if it is used for usage) and that equality
-- reflection is not allowed or the context is empty.

module _
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  ⦃ ok : No-equality-reflection or-empty Δ ⦄
  where

  open Imports factoring-nr

  opaque

    ⇾→⊢⇒ : Δ ⊢ₛ s ∷ A → s ⇾ s′ → Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
    ⇾→⊢⇒ {s} ⊢s (⇾ₑ d) =
      subst (_ ⊢ _ ⇒*_∷ _) (⇾ₑ-⦅⦆-≡ d) (id (⊢⦅⦆ {s = s} ⊢s))
    ⇾→⊢⇒ ⊢s (⇒ᵥ d) =
      redMany (⇒ᵥ→⇒ ⊢s d)

  opaque

    ⇾*→⊢⇒* : Δ ⊢ₛ s ∷ A → s ⇾* s′ → Δ ⊢ ⦅ s ⦆ ⇒* ⦅ s′ ⦆ ∷ A
    ⇾*→⊢⇒* {s} ⊢s id = id (⊢⦅⦆ {s = s} ⊢s)
    ⇾*→⊢⇒* {s = record{}} ⊢s (_⇨_ {s₂ = record{}} x d) =
      ⇾→⊢⇒ ⊢s x ⇨∷* ⇾*→⊢⇒* (⊢ₛ-⇾ ⊢s x) d

  opaque

    ⊢⇒→⇒ᵥ : Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A
          → Normal s
          → Δ ⊢ₛ s ∷ B
          → ∃₃ λ m n (s′ : State _ m n) → s ⇒ᵥ s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒→⇒ᵥ {s = ⟨ H , t , ρ , ε ⟩} d (val x) ⊢s =
      case Value→Whnf (substValue (toSubstₕ H) (wkValue ρ x)) of λ where
          (inj₁ w) → ⊥-elim (whnfRedTerm d w)
          (inj₂ (_ , _ , _ , _ , _ , _ , ≡ur , η)) →
            case subst-unitrec {t = wk ρ t} ≡ur of λ where
              (inj₁ (_ , ≡x)) → case subst Value ≡x (wkValue ρ x) of λ ()
              (inj₂ (_ , _ , _ , ≡ur′ , refl , refl , refl)) →
                case wk-unitrec ≡ur′ of λ {
                  (_ , _ , _ , refl , refl , refl , refl) →
                _ , _ , _ , unitrec-ηₕ η , lemma η d}
        where
        lemma : Unitʷ-η → Δ ⊢ (unitrec l p q A u v) ⇒ w ∷ B → w PE.≡ v
        lemma η (conv d x) = lemma η d
        lemma η (unitrec-subst _ _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β _ _ _ no-η) = ⊥-elim (no-η η)
        lemma η (unitrec-β-η _ _ _ _ _) = refl
    ⊢⇒→⇒ᵥ {s = ⟨ H , t , ρ , e ∙ S ⟩} d (val v) ⊢s =
      case ⊢Value-⇒ᵥ ⊢s v of λ
        (_ , _ , _ , d′) →
      _ , _ , _ , d′ , whrDetTerm d (⇒ᵥ→⇒ ⊢s d′)
    ⊢⇒→⇒ᵥ d (var d′) ⊢s =
      let _ , _ , _ , _ , ⊢S = ⊢ₛ-inv ⊢s
      in  ⊥-elim (neRedTerm d (NeutralAt→Neutral
            (toSubstₕ-NeutralAt d′ (⊢⦅⦆ˢ-NeutralAt ⊢S var))))

-- The remaining properties are proven under some additional assumptions

module _ (As : Assumptions) where

  open Assumptions As
  open Imports factoring-nr
  open import Graded.Heap.Usage.Reduction type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available

  opaque

    ⊢⇒→⇾* :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      Δ ⊢ ⦅ s ⦆ ⇒ u ∷ A →
      Δ ⊢ₛ s ∷ B →
      ▸ s →
      ∃₃ λ m n (s′ : State _ m n) → s ⇾* s′ × u PE.≡ ⦅ s′ ⦆
    ⊢⇒→⇾* {s} d ⊢s ▸s =
      let _ , s′ , n , d′ = ▸normalize As s ▸s
          d″ = PE.subst (_ ⊢_⇒ _ ∷ _) (⇾ₑ*-⦅⦆-≡ d′) d
          ⊢s′ = ⊢ₛ-⇾ₑ* ⊢s d′
          _ , _ , s″ , d‴ , u≡ = ⊢⇒→⇒ᵥ factoring-nr d″ n ⊢s′
      in  _ , _ , s″ , ⇾ₑ* d′ ⇨* ⇒ᵥ d‴ ⇨ id , u≡

  opaque

    ⊢⇒*→⇾* :
      ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
      Δ ⊢ ⦅ s ⦆ ⇒* u ∷ A →
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
